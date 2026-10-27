module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Final
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTrialityThreeChars

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.HardMathSupport.Lang.Coordinator

theorem outerFixedOrderTrialityThreeChar_two :
    OuterFixedOrderTrialityThreeChar (· = 2) := by
  intro K _ _ n ℓ f hℓ hadm hmodel α hα3 hαin
  subst hℓ
  exact Or.inr (outerFixedOrder_trialityD4_three_even K n f hadm hmodel α hα3 hαin)

end CFSG.HardMathSupport.Lang.E6Descent
