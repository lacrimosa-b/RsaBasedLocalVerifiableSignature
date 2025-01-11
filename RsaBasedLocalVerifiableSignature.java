import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import javax.crypto.Mac;
import javax.crypto.spec.SecretKeySpec;

public class RsaBasedLocalVerifiableSignature {
    
    public static class PRF {

        public static String Setup(int lambdaBits) {
            SecureRandom random = new SecureRandom();
            byte[] key = new byte[lambdaBits / 8]; 
            random.nextBytes(key);
            return bytesToHex(key);
        }

        public static BigInteger Eval(String K, String mCount, int lambdaBits) {
            try {
                Mac hmac = Mac.getInstance("HmacSHA256");
                SecretKeySpec keySpec = new SecretKeySpec(hexToBytes(K), "HmacSHA256");
                hmac.init(keySpec);

                byte[] input = mCount.getBytes();
                byte[] prfResult = hmac.doFinal(input);

                byte[] lambdaOutput = Arrays.copyOf(prfResult, lambdaBits / 8);
                return new BigInteger(1, lambdaOutput); 

            } catch (Exception e) {
                e.printStackTrace();
                return null;
            }
        }

        private static String bytesToHex(byte[] bytes) {
            StringBuilder hexString = new StringBuilder();
            for (byte b : bytes) {
                hexString.append(String.format("%02x", b));
            }
            return hexString.toString();
        }

        private static byte[] hexToBytes(String hex) {
            int length = hex.length();
            byte[] bytes = new byte[length / 2];
            for (int i = 0; i < length; i += 2) {
                bytes[i / 2] = (byte) ((Character.digit(hex.charAt(i), 16) << 4)
                        + Character.digit(hex.charAt(i + 1), 16));
            }
            return bytes;
        }
    }

    public static class PrimeSeqPRF {
        private int lambdaBits;

        public PrimeSeqPRF(int lambdaBits) {
            this.lambdaBits = lambdaBits;
        }

        public String PrimeSeq() {
            String K = PRF.Setup(this.lambdaBits); 
            return K;
        }

        public BigInteger PrimeSamp(String K, String m, int lambdaBits) {
            int count = 0;
            boolean flag = false;
            BigInteger e = BigInteger.ZERO;

            while (!flag) {
                String mCount = m + count;
                BigInteger y = PRF.Eval(K, mCount, lambdaBits); 
                BigInteger candidate = BigInteger.ONE.shiftLeft(lambdaBits).add(y).add(BigInteger.ONE); 
                if (isPrime(candidate)) {
                    flag = true;
                    e = candidate;
                } else {
                    count++;
                }
            }
            return e;
        }

        private boolean isPrime(BigInteger num) {
            return num.isProbablePrime(10); 
        }
    }

    public static class Signature {
        private PrimeSeqPRF primeSeqPRF;
        private BigInteger p, q, n, g;
        private String sk, vk;

        public Signature(int lambdaBits) {
            this.primeSeqPRF = new PrimeSeqPRF(lambdaBits);
        }

        public String GenKey() {
            p = BigInteger.probablePrime(512, new SecureRandom()); 
            q = BigInteger.probablePrime(512, new SecureRandom()); 
            this.n = p.multiply(q); 
            this.g = new BigInteger(1024, new SecureRandom()).mod(this.n); 
    
            String samp = this.primeSeqPRF.PrimeSeq(); 

            this.vk = n.toString() + ":" + samp + ":" + g.toString();
            this.sk = p.toString() + ":" + q.toString() + ":" + samp + ":" + g.toString();
    
            return this.vk;
        }
    
        public BigInteger Sign(String m) {
            String K = this.sk.split(":")[2]; 
            BigInteger e = this.primeSeqPRF.PrimeSamp(K, m, 1024); 
            BigInteger phi = this.p.subtract(BigInteger.ONE).multiply(this.q.subtract(BigInteger.ONE));
            BigInteger invE = e.modInverse(phi);
            BigInteger sig = g.modPow(invE, this.p.multiply(this.q));
            return sig;
        }

        public boolean Verify(String vk, String m, BigInteger sig) {
            String[] vkParts = vk.split(":");
            BigInteger n = new BigInteger(vkParts[0]);
            String K = vkParts[1]; 
            BigInteger e = this.primeSeqPRF.PrimeSamp(K, m, 1024);
            return sig.modPow(e, n).equals(new BigInteger(vkParts[2]));
        }

        public BigInteger Aggregate(String vk, List<String> mList, List<BigInteger> sigList) {
            BigInteger aggSig = BigInteger.ONE;

            for (int i = 0; i < mList.size(); i++) {
                if (!Verify(vk, mList.get(i), sigList.get(i))) {
                    return BigInteger.valueOf(-1); 
                }
                aggSig = aggSig.multiply(sigList.get(i)).mod(new BigInteger(vk.split(":")[0])); 
            }

            return aggSig;
        }

        public boolean AggVerify(String vk, List<String> mList, BigInteger aggSig) {
            String[] vkParts = vk.split(":");
            BigInteger n = new BigInteger(vkParts[0]);
            BigInteger prod = BigInteger.ONE;
            for (String m : mList) {
                BigInteger e = this.primeSeqPRF.PrimeSamp(vkParts[1], m, 1024);
                prod = prod.multiply(e);
            }

            BigInteger check = BigInteger.ONE;
            for (String m : mList) {
                BigInteger e = this.primeSeqPRF.PrimeSamp(vkParts[1], m, 1024);
                check = check.multiply(g.modPow(prod.divide(e), n)).mod(n);
            }

            return aggSig.modPow(prod, n).equals(check); 
        }

        public BigInteger LocalOpen(BigInteger aggSig, String vk, List<String> mList, int j) {
            String[] vkParts = vk.split(":");
            BigInteger n = new BigInteger(vkParts[0]);
            BigInteger[] eList = new BigInteger[mList.size()];
            BigInteger prod = BigInteger.ONE;
            BigInteger e_mj = BigInteger.ONE;

            for (int i = 0; i < mList.size(); i++) {
                String m = mList.get(i);
                eList[i] = this.primeSeqPRF.PrimeSamp(vkParts[1], m, 1024);
                prod = prod.multiply(eList[i]);
                if (i != j) {
                    e_mj = e_mj.multiply(eList[i]);
                }
            }

            if (eList[j].gcd(e_mj).equals(BigInteger.ONE)) {
                BigInteger f_j = BigInteger.ZERO;
                for (int i = 0; i < mList.size(); i++) {
                    if (i != j) {
                        f_j = f_j.add(e_mj.divide(eList[i]));
                    }
                }

                BigInteger x = aggSig.modPow(e_mj, n).multiply(g.modPow(f_j, n).modInverse(n));
                BigInteger[] exgcd = exgcd(eList[j], e_mj);
                BigInteger alpha = exgcd[0], beta = exgcd[1];
                return g.modPow(alpha, n).multiply(x.modPow(beta, n)).mod(n); 
            } else {
                return BigInteger.valueOf(-1); 
            }
        }

        private BigInteger[] exgcd(BigInteger a, BigInteger b) {
            if (b.equals(BigInteger.ZERO)) {
                return new BigInteger[] {BigInteger.ONE, BigInteger.ZERO};
            }
            BigInteger[] result = exgcd(b, a.mod(b));
            BigInteger x = result[0], y = result[1];
            return new BigInteger[] {y, x.subtract(a.divide(b).multiply(y))};
        }

        public boolean LocalAggVerify(BigInteger aggSig, String vk, String m, BigInteger aux) {
            return Verify(vk, m, aux); 
        }
    }

    public static void main(String[] args) {
        int lambdaBits = 1024;
        Signature aggsig = new Signature(lambdaBits);
        String vk = aggsig.GenKey(); 

        List<String> mList = new ArrayList<>();
        for (int i = 0; i < 5; i++) {
            mList.add(generateRandomString(16)); 
        }
        
        // Generate signatures for each message
        long startTime = System.currentTimeMillis();
        List<BigInteger> sigList = new ArrayList<>();
        for (String m : mList) {
            sigList.add(aggsig.Sign(m)); 
        }
        System.out.println("Sign finished.");
        long endTime = System.currentTimeMillis();
        long executionTime = endTime - startTime;
        System.out.println("Sign time: " + executionTime + " ms\n");
        
        // Verify test
        startTime = System.currentTimeMillis();
        for(int i = 0; i <mList.size(); i++) {
            System.out.println("Verify result for message " + i + ":" + aggsig.Verify(vk, mList.get(i), sigList.get(i)));
        }
        System.out.println("Verify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("Verify time: " + executionTime + " ms\n");

        // Aggregate the signatures
        startTime = System.currentTimeMillis();
        BigInteger aggSig = aggsig.Aggregate(vk, mList, sigList);
        System.out.println("Aggregated Signature: " + aggSig);
        System.out.println("Aggregate finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("Aggregate time: " + executionTime + " ms\n");

        // AggVerify test
        startTime = System.currentTimeMillis();
        boolean isValid = aggsig.AggVerify(vk, mList, aggSig);
        System.out.println("AggVerify result: " + isValid);
        System.out.println("AggVerify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("AggVerify time: " + executionTime + " ms\n");

        // LocalOpen
        startTime = System.currentTimeMillis();
        List<BigInteger> auxList = new ArrayList<>();
        for (int i = 0; i < mList.size(); i++) {
            auxList.add(aggsig.LocalOpen(aggSig, vk, mList, i));
        }
        System.out.println("LocalOpen finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("LocalOpen time: " + executionTime + " ms\n");

        // LocalAggVerify test
        startTime = System.currentTimeMillis();
        for (int i = 0; i < mList.size(); i++) {
            boolean localVerified = aggsig.LocalAggVerify(aggSig, vk, mList.get(i), auxList.get(i));
            System.out.println("LocalAggVerify result for message " + i + ": " + localVerified);
        }
        System.out.println("LocalAggVerify finished.");
        endTime = System.currentTimeMillis();
        executionTime = endTime - startTime;
        System.out.println("LocalAggVerify time: " + executionTime + " ms\n");
    }

    // generate random string for message
    public static String generateRandomString(int length) {
        String characters = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
        Random rand = new Random();
        StringBuilder s = new StringBuilder(length);
        for (int i = 0; i < length; i++) {
            s.append(characters.charAt(rand.nextInt(characters.length())));
        }
        return s.toString();
    }
}
