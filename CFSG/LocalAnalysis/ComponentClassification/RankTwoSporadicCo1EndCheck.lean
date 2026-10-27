module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1End
public import Certificates.Certificate15049

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

theorem co1_endCheck : co1EndCheck co1EndD co1EndIdx co1EndDB =
    true :=
  Certificates.certificate15049

theorem sporadicCaseOdd_Co1
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) :
    SporadicCaseOdd .Co1 :=
  sporadicCaseOdd_Co1_of_check co1_endCheck h32 h33

end CFSG.ComponentClassification.RankTwoSporadic.Co1
