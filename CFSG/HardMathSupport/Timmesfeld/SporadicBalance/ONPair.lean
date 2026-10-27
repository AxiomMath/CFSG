module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONWitness
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONOuter

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem sporadicOnePairHolds_ONan_three :
    SporadicOnePairHolds .ONan 3 :=
  ⟨sporadicOPrimeHolds_ONan_three, sporadicOuterHolds_ONan_three⟩

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
