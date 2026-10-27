module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.ClosingOdd
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator.PhiRows

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator

open TauCeti CFSG.LieType.SeitzGeneration


theorem longTorusClosingOdd_proved :
    LongTorusClosingOdd := by
  intro ℓ f hℓ hℓ2 hf K _ _ hK σ hσ
  exact Inner.longTorusClosing_of_fields hℓ hℓ2 hf hK σ hσ

end CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator
