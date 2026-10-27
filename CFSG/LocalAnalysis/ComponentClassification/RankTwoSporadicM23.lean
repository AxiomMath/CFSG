module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM23Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.M23

theorem sporadicCaseOdd_M23 (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .M23 :=
  sporadicCaseOdd_M23_of (CFSG.Sporadic.Schreier.inner_eq_top_of_card_le
    CFSG.Sporadic.Schreier.m23_center_eq_bot' CFSG.Sporadic.Schreier.m23_mulAut_card) h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.M23
