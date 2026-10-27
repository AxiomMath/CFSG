module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBCommDefs
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate15048
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBCommB

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.B

theorem b_twoACheck : TwoAClassData :=
  Certificates.certificate15048

theorem sporadicCaseOdd_B_of_classFacts
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) (h2C : B2CFact) (h2D : B2DFact) :
    SporadicCaseOdd .B :=
  sporadicCaseOdd_B_of_facts h32 h33 b_twoACheck h2C h2D

end CFSG.ComponentClassification.RankTwoSporadic.B
