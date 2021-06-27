package negotiator.ahbuneagent;

import geniusweb.actions.*;
import geniusweb.bidspace.AllBidsList;
import geniusweb.issuevalue.Bid;
import geniusweb.issuevalue.Value;
import geniusweb.party.Capabilities;
import geniusweb.party.DefaultParty;
import geniusweb.party.inform.*;
import geniusweb.profile.FullOrdering;
import geniusweb.profile.PartialOrdering;
import geniusweb.profileconnection.ProfileConnectionFactory;
import geniusweb.profileconnection.ProfileInterface;
import geniusweb.progress.Progress;
import geniusweb.progress.ProgressRounds;
import negotiator.ahbuneagent.impmap.SimilarityMap;
import negotiator.ahbuneagent.impmap.OppSimilarityMap;
import negotiator.ahbuneagent.linearorder.OppSimpleLinearOrdering;
import negotiator.ahbuneagent.linearorder.SimpleLinearOrdering;
import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.ParseException;
import tudelft.utilities.logging.Reporter;

import javax.websocket.DeploymentException;
import java.io.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.*;
import java.util.logging.Level;
import java.util.stream.Collectors;

import org.json.simple.parser.JSONParser;

import static java.lang.Math.*;

public class AhBuNeAgent extends DefaultParty {
    private final Random random = new Random();

    private int ourNumFirstBids;
    private int ourNumLastBids;
    private int oppNumFirstBids;
    private int ourKnownBidNum = 0;
    private int oppKnownBidNum = 0;


    protected ProfileInterface profileInterface;
    private PartyId partyId;
    private Progress progress;
    private double time = 0.0;

    private AllBidsList allPossibleBids;
    private BigInteger allPossibleBidsSize;
    private SimpleLinearOrdering ourLinearPartialOrdering = null;
    private OppSimpleLinearOrdering oppLinearPartialOrdering = null;
    private SimilarityMap ourSimilarityMap = null;
    private OppSimilarityMap oppSimilarityMap = null;

    private Bid lastReceivedBid = null;
    private double utilityLowerBound = 1.0;
    private final double ourMaxCompromise = 0.1;

    // Initially no loss
    private double lostElicitScore = 0.00;
    //Set default as 0.01 by Genius Framework
    private double elicitationCost = 0.01;
    private final BigDecimal maxElicitationLost = new BigDecimal("0.05");
    private int leftElicitationNumber = 0;
    Bid elicitationBid = null;
    ArrayList<Map.Entry<Bid, Integer>> mostCompromisedBids = new ArrayList<>();
    ArrayList<Bid> oppElicitatedBid = new ArrayList<>();
    private Bid reservationBid = null;

    HashMap<String, HashMap<String, BigDecimal>> issueUtilities;
    HashMap<String, BigDecimal> issueWeights;

    public AhBuNeAgent() {
        this.parseJson();
    }

    public AhBuNeAgent(Reporter reporter) {
        super(reporter);
        this.parseJson();
    }

    @Override
    public Capabilities getCapabilities() {
        return new Capabilities(new HashSet<>(Arrays.asList("SHAOP", "SAOP")));
    }

    @Override
    public String getDescription() {
        return "AhBuNe Agent";
    }

    @Override
    public void notifyChange(Inform info) {
        try {
            if (info instanceof Settings) {
                Settings settings = (Settings) info;
                init(settings);
            } else if (info instanceof ActionDone) {
                Action lastReceivedAction = ((ActionDone) info).getAction();
                if (lastReceivedAction instanceof Offer) {
                    lastReceivedBid = ((Offer) lastReceivedAction).getBid();
                } else if (lastReceivedAction instanceof Comparison) {
                    ourLinearPartialOrdering = ourLinearPartialOrdering.with(((Comparison) lastReceivedAction).getBid(), ((Comparison) lastReceivedAction).getWorse());
                    myTurn();
                }
            } else if (info instanceof YourTurn) {
                if (progress instanceof ProgressRounds) {
                    progress = ((ProgressRounds) progress).advance();
                }
                myTurn();
            } else if (info instanceof Finished) {
            }
        } catch (Exception exception) {
            throw new RuntimeException("Failed to handle info", exception);
        }
    }

    private void init(Settings settings) throws IOException, DeploymentException {
        this.partyId = settings.getID();
        this.progress = settings.getProgress();
        this.profileInterface = ProfileConnectionFactory.create(settings.getProfile().getURI(), getReporter());

        if (profileInterface.getProfile() instanceof FullOrdering) {
            throw new UnsupportedOperationException("Only <DefaultPartialOrdering> is supported");
        } else if (profileInterface.getProfile() instanceof PartialOrdering) {
            PartialOrdering partialProfile = (PartialOrdering) profileInterface.getProfile();
            this.allPossibleBids = new AllBidsList(partialProfile.getDomain());
            this.allPossibleBidsSize = allPossibleBids.size();
            this.ourSimilarityMap = new SimilarityMap(partialProfile);
            this.oppSimilarityMap = new OppSimilarityMap(partialProfile);
            this.ourLinearPartialOrdering = new SimpleLinearOrdering(profileInterface.getProfile());
            this.oppLinearPartialOrdering = new OppSimpleLinearOrdering();
            this.ourSimilarityMap.update(ourLinearPartialOrdering);
            getReservationRatio();
            getElicitationCost(settings);
            // calculateBidUtility(this.ourLinearPartialOrdering.getMaxBid());
        } else {
            throw new UnsupportedOperationException("Only <DefaultPartialOrdering> is supported");
        }

    }

    private Action selectAction() {
        if (doWeMakeElicitation()) {
            lostElicitScore += elicitationCost;
            leftElicitationNumber -= 1;
            return new ElicitComparison(partyId, elicitationBid, ourLinearPartialOrdering.getBids());
        }

        if (lastReceivedBid == null) {
            return makeAnOffer();
        }
        if (doWeEndTheNegotiation()) {
            return new EndNegotiation(partyId);
        } else if (doWeAccept(lastReceivedBid)) {
            return new Accept(partyId, lastReceivedBid);
        }
        return makeAnOffer();

    }

    private void myTurn() throws IOException {
        time = progress.get(System.currentTimeMillis());
        strategySelection();
        Action action = selectAction();
        getConnection().send(action);
    }

    private boolean doWeEndTheNegotiation() {
        if (reservationBid != null && ourSimilarityMap.isCompatibleWithSimilarity(reservationBid, ourNumFirstBids, ourNumLastBids, 0.9 - time * 0.1)) {
            return true;
        }
        return false;
    }

    private Bid elicitationRandomBidGenerator() {
        Bid foundBid = allPossibleBids.get(random.nextInt(allPossibleBids.size().intValue()));
        while (ourLinearPartialOrdering.getBids().contains(foundBid)) {
            foundBid = allPossibleBids.get(random.nextInt(allPossibleBids.size().intValue()));
        }
        return foundBid;
    }

    private Action makeAnOffer() {
        if (time > 0.96) {
            for (int i = ourLinearPartialOrdering.getKnownBidsSize() - 1; i >= 0; i--) {
                Bid testBid = ourLinearPartialOrdering.getBidByIndex(i);
                if (oppElicitatedBid.contains(testBid) && doWeAccept(testBid)) {
                    calculateBidUtility(testBid);
                    return new Offer(partyId, testBid);
                }
            }
        }
        Bid oppMaxBid = oppLinearPartialOrdering.getMaxBid();
        // calculateBidUtility(oppMaxBid)
        Bid ourOffer = ourSimilarityMap.findBidCompatibleWithSimilarity(ourNumFirstBids, ourNumLastBids, utilityLowerBound, oppMaxBid);
        if (time < 0.015) {
            if (oppLinearPartialOrdering.isAvailable()) {
                int count = 0;
                // ilk tekliflerde hiçbir zaman teklif olqrka max bidi göndermeme eğilimi
                while (count < 500 && !oppSimilarityMap.isCompromised(ourOffer, oppNumFirstBids, 0.85) && ourOffer.equals(ourLinearPartialOrdering.getMaxBid())) {
                    ourOffer = ourSimilarityMap.findBidCompatibleWithSimilarity(ourNumFirstBids, ourNumLastBids, 0.85, oppMaxBid);
                    count++;
                }
            } else {
                int count = 0;
                while (count < 500 && ourOffer.equals(ourLinearPartialOrdering.getMaxBid())) {
                    ourOffer = ourSimilarityMap.findBidCompatibleWithSimilarity(ourNumFirstBids, ourNumLastBids, 0.85, oppMaxBid);
                    count++;
                }
            }
        } else if (lastReceivedBid != null) {
            if (ourSimilarityMap.isCompatibleWithSimilarity(lastReceivedBid, ourNumFirstBids, ourNumLastBids, 0.9)) {
                return new Offer(partyId, lastReceivedBid);
            }
            if (ourSimilarityMap.isCompatibleWithSimilarity(oppMaxBid, ourNumFirstBids, ourNumLastBids, 0.9)) {
                return new Offer(partyId, oppMaxBid);
            }
            int count = 0;
            while (count < 500 && oppLinearPartialOrdering.isAvailable() && !oppSimilarityMap.isCompromised(ourOffer, oppNumFirstBids, utilityLowerBound)) {
                ourOffer = ourSimilarityMap.findBidCompatibleWithSimilarity(ourNumFirstBids, ourNumLastBids, utilityLowerBound, oppMaxBid);
            }
        }
        getReporter().log(Level.INFO, "Our offer utility");
        calculateBidUtility(ourOffer);
        return new Offer(partyId, ourOffer);
    }


    private boolean doWeAccept(Bid bid) {
        if (ourSimilarityMap.isCompatibleWithSimilarity(bid, ourNumFirstBids, ourNumLastBids, 0.9)) {
            return true;
        }

        double startUtilitySearch = utilityLowerBound;

        if (time >= 0.98) {
            startUtilitySearch = utilityLowerBound - ourMaxCompromise;
        }

        if (oppLinearPartialOrdering.isAvailable()) {
            for (int i = (int) (startUtilitySearch * 100); i <= 95; i += 5) {
                double utilityTest = (double) i / 100.0;
                if (oppSimilarityMap.isCompromised(bid, oppNumFirstBids, utilityTest)) {
                    if (ourSimilarityMap.isCompatibleWithSimilarity(bid, ourNumFirstBids, ourNumLastBids, utilityTest)) {
                        return true;
                    }
                    break;
                }
            }
        }
        return false;
    }

    private boolean doWeMakeElicitation() {
        if (leftElicitationNumber == 0) {
            return false;
        }
        if (allPossibleBidsSize.intValue() <= 100) {
            if (ourLinearPartialOrdering.getKnownBidsSize() < allPossibleBidsSize.intValue() * 0.1) {
                elicitationBid = elicitationRandomBidGenerator();
                return true;
            }
        } else if (ourLinearPartialOrdering.getKnownBidsSize() < 10) {
            elicitationBid = elicitationRandomBidGenerator();
            return true;
        } else if (time > 0.98 && oppLinearPartialOrdering.isAvailable()) {
            if (mostCompromisedBids.size() > 0) {
                elicitationBid = mostCompromisedBids.remove(mostCompromisedBids.size() - 1).getKey();
                oppElicitatedBid.add(elicitationBid);
                return true;
            } else {
                LinkedHashMap<Bid, Integer> mostCompromisedBidsHash = oppSimilarityMap.mostCompromisedBids();
                Set<Map.Entry<Bid, Integer>> sortedCompromiseMapSet = mostCompromisedBidsHash.entrySet();
                mostCompromisedBids = new ArrayList<>(sortedCompromiseMapSet);
                elicitationBid = mostCompromisedBids.remove(mostCompromisedBids.size() - 1).getKey();
                oppElicitatedBid.add(elicitationBid);
                return true;
            }
        }
        return false;
    }

    private void strategySelection() {
        utilityLowerBound = getUtilityLowerBound(time, lostElicitScore);
        ourKnownBidNum = ourLinearPartialOrdering.getKnownBidsSize();
        oppKnownBidNum = oppLinearPartialOrdering.getKnownBidsSize();
        ourNumFirstBids = getNumFirst(utilityLowerBound, ourKnownBidNum);
        ourNumLastBids = getNumLast(utilityLowerBound, getUtilityLowerBound(1.0, lostElicitScore), ourKnownBidNum);
        if (lastReceivedBid != null) {
            oppLinearPartialOrdering.updateBid(lastReceivedBid);
            oppSimilarityMap.update(oppLinearPartialOrdering);
            oppNumFirstBids = getOppNumFirst(utilityLowerBound, oppKnownBidNum);
        }
    }

    private void getElicitationCost(Settings settings) {
        try {
            elicitationCost = Double.parseDouble(settings.getParameters().get("elicitationcost").toString());
            leftElicitationNumber = (int) (maxElicitationLost.doubleValue() / elicitationCost);
            reporter.log(Level.INFO, "leftElicitationNumber: " + leftElicitationNumber);
        } catch (Exception e) {
            elicitationCost = 0.01;
            leftElicitationNumber = (int) (maxElicitationLost.doubleValue() / elicitationCost);
            reporter.log(Level.INFO, "catch leftElicitationNumber: " + leftElicitationNumber);
        }
    }

    private void getReservationRatio() {
        try {
            reservationBid = profileInterface.getProfile().getReservationBid();
        } catch (Exception e) {
            reservationBid = null;
        }
    }

    double getUtilityLowerBound(double time, double lostElicitScore) {
        if (time < 0.5) {
            return -pow((time - 0.25), 2) + 0.9 + lostElicitScore;
        } else if (time < 0.7) {
            return -pow((1.5 * (time - 0.7)), 2) + 0.9 + lostElicitScore;
        }
        return (3.25 * time * time) - (6.155 * time) + 3.6105 + lostElicitScore;
    }

    int getNumFirst(double utilityLowerBound, int knownBidNum) {
        return ((int) (knownBidNum * (1 - utilityLowerBound)) + 1);
    }

    int getNumLast(double utilityLowerBound, double minUtilityLowerBound, int ourKnownBidNum) {
        return ((int) (ourKnownBidNum * (1 - minUtilityLowerBound)) - (int) (ourKnownBidNum * (1 - utilityLowerBound)) + 1);
    }

    int getOppNumFirst(double utilityLowerBound, int oppKnownBidNum) {
        return ((int) (oppKnownBidNum * (1 - utilityLowerBound)) + 1);
    }

    void parseJson() {
        this.issueUtilities = new HashMap<>();
        this.issueWeights = new HashMap<>();
        try {
            ClassLoader classLoader = getClass().getClassLoader();
            InputStream stream = classLoader.getResourceAsStream("parties/party1.json");
            JSONObject object = inputStreamToJsonObject(stream);

            JSONParser parser = new JSONParser();
            JSONObject json = (JSONObject) parser.parse(object.get("LinearAdditiveUtilitySpace").toString());

            JSONParser parser1_1 = new JSONParser();
            JSONObject json1_1 = (JSONObject) parser1_1.parse(json.get("issueWeights").toString());
            for (Object key : json1_1.keySet()) {
                issueWeights.put(String.valueOf(key), BigDecimal.valueOf((Double) json1_1.get(key)));
            }

            JSONParser parser1_2 = new JSONParser();
            JSONObject json1_2 = (JSONObject) parser1_2.parse(json.get("issueUtilities").toString());
            for (Object key : json1_2.keySet()) {
                JSONParser parser1_4 = new JSONParser();
                JSONObject json1_2_0 = (JSONObject) parser1_4.parse(json1_2.get(key).toString());
                JSONParser parser1_3 = new JSONParser();
                JSONObject json1_2_1 = (JSONObject) parser1_3.parse(json1_2_0.get("discreteutils").toString());
                JSONParser parser1_5 = new JSONParser();
                JSONObject json1_2_1_1 = (JSONObject) parser1_5.parse(json1_2_1.get("valueUtilities").toString());

                HashMap<String, BigDecimal> tempMap = new HashMap<>();
                for (Object key2 : json1_2_1_1.keySet()) {
                    JSONParser parser1_6 = new JSONParser();
                    BigDecimal value;
                    try {
                        value = BigDecimal.valueOf((Double) json1_2_1_1.get(key2));
                    } catch (Exception e) {
                        value = BigDecimal.valueOf((Long) json1_2_1_1.get(key2));
                    }
                    //getReporter().log(Level.INFO, "ss" + value);
                    tempMap.put("" + key2, value);
                }
                issueUtilities.put("" + key, tempMap);
            }
            getReporter().log(Level.INFO, "ss" + issueUtilities.get("Invitations").get("Plain"));
        } catch (Exception e) {
            getReporter().log(Level.INFO, "error first");
            e.printStackTrace();
        }
    }

    private void parseEmployeeObject(JSONObject employee) {
        //Get employee object within list
        JSONObject employeeObject = (JSONObject) employee.get("employee");

        //Get employee first name
        String firstName = (String) employeeObject.get("firstName");
        System.out.println(firstName);

        //Get employee last name
        String lastName = (String) employeeObject.get("lastName");
        System.out.println(lastName);

        //Get employee website name
        String website = (String) employeeObject.get("website");
        System.out.println(website);
    }

    public JSONObject inputStreamToJsonObject(InputStream inputStream) throws IOException, ParseException {
        JSONParser jsonParser = new JSONParser();
        return (JSONObject) jsonParser.parse(
                new InputStreamReader(inputStream, "UTF-8"));
    }

    private BigDecimal calculateBidUtility(Bid bid) {
        BigDecimal utility = new BigDecimal(0);
        for (String issue : bid.getIssues()) {
            BigDecimal one = issueUtilities.get(issue).get(removeFirstandLast(String.valueOf(bid.getValue(issue))));
            BigDecimal two = issueWeights.get(issue);
            BigDecimal three = two.multiply(one);
            utility = utility.add(three);
        }
        getReporter().log(Level.INFO, "Utility" + utility.doubleValue());
        return utility;
    }
    String removeFirstandLast(String str)
    {

        // Creating a StringBuilder object
        StringBuilder sb = new StringBuilder(str);

        // Removing the last character
        // of a string
        sb.deleteCharAt(str.length() - 1);

        // Removing the first character
        // of a string
        sb.deleteCharAt(0);

        // Converting StringBuilder into a string
        // and return the modified string
        return sb.toString();
    }
    public static void main(String args[]) {
        //AhBuNeAgent agent = new AhBuNeAgent();
        //agent.parseJson();
        //agent.calculateBidUtility(new Bid());


    }
}
