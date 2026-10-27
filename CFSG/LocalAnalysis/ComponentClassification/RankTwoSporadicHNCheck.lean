module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHN
public import Certificates.Certificate15020
public import Certificates.Certificate15021

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

theorem hn_t4Check : hnT4Check (decodePoolT4 hnT4PoolStr)
    (decodeT4 hnT4WitStr) = true :=
  Certificates.certificate15020

theorem hn_aCheck : hnAOCheck (decodePairsO hnAProgStr) hnAPregs
    (decodePairsO hnAPoolStr).toArray (decodeAO hnAWitStr) = true :=
  Certificates.certificate15021

theorem sporadicCaseOdd_HN
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .HN :=
  sporadicCaseOdd_HN_of_check hn_t4Check hn_aCheck h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.HN
