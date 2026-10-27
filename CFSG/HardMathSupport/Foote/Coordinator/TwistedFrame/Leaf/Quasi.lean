module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxMain
import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6Lift

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


section E6Sc

private theorem twQuasi_e6Six_X₂ : E6SixX₂Statement :=
  e6SixX₂_of_sc QuasiE6Lift.e6Sc

theorem twQuasi (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwQuasi (c.X₁ D) (c.X₂ D) :=
  twQuasi_of_e6Six_X₂ twQuasi_e6Six_X₂ c K hK D

end E6Sc

theorem twQuasi_of_ne_e6Six (c : TwClass) (hc : c ≠ TwClass.e6Six) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) : TwQuasi (c.X₁ D) (c.X₂ D) :=
  ⟨twQuasi_X₁ c K hK D, twQuasi_X₂_of_ne_e6Six c hc K hK D⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
