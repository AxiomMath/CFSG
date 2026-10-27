module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22CheckII
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Check17
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicStandard17

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M22

theorem sporadicCaseOdd_M22 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .M22 :=
  sporadicCaseOdd_of_yCensus17 h32 h33 m22AutModel m22_commutator_le
    m22_yCensusII_cert m22_yCensus17_cert

end CFSG.ComponentClassification.RankTwoSporadic.M22
