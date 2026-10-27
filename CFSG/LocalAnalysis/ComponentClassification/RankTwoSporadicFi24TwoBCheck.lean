module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoB
public import Certificates.Certificate15027
public import Certificates.Certificate15028

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

theorem fi24_twoBKCheck : fi24TwoBKCheck = true :=
  Certificates.certificate15027

theorem fi24_twoBJCheck :
    TwoBJFacts :=
  Certificates.certificate15028

theorem twoB_facts_checked :
    TwoBPerfect ∧ TwoBQ fi24QR ∧ TwoBIrreducible fi24QR ∧ TwoBFaithful fi24QR ∧
      TwoBOrderFour fi24QR ∧ TwoBCentralizer :=
  twoB_facts fi24_twoBKCheck fi24_twoBJCheck

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
