module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxF4
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE6
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE8Ten
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.QuasiAuxE8Twelve

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

set_option linter.unusedSectionVars false


theorem twQuasi_X₁ (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : CFSG.IsQuasisimple ↥(c.X₁ D) := by
  cases c
  · exact isQuasisimple_f4Six_X₁ hK D
  · exact isQuasisimple_e6Six_X₁ hK D
  · exact isQuasisimple_e8Ten_X₁ D
  · exact isQuasisimple_e8Twelve_X₁ D

theorem twQuasi_X₂_of_ne_e6Six (c : TwClass) (hc : c ≠ TwClass.e6Six) (K : Type) [Field K]
    [Finite K] (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) :
    CFSG.IsQuasisimple ↥(c.X₂ D) := by
  cases c
  · exact isQuasisimple_f4Six_X₂ hK D
  · exact absurd rfl hc
  · exact isQuasisimple_e8Ten_X₂ D
  · exact isQuasisimple_e8Twelve_X₂ D

@[expose] def E6SixX₂Statement : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 3 ≤ Nat.card K →
    ∀ D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w,
      CFSG.IsQuasisimple ↥(TwClass.e6Six.X₂ D)

theorem twQuasi_of_e6Six_X₂ (h : E6SixX₂Statement) (c : TwClass) (K : Type) [Field K] [Finite K]
    (hK : c.minQ ≤ Nat.card K) (D : LangLevi c.tag K c.w) : TwQuasi (c.X₁ D) (c.X₂ D) := by
  refine ⟨twQuasi_X₁ c K hK D, ?_⟩
  by_cases hc : c = TwClass.e6Six
  · subst hc
    exact h K hK D
  · exact twQuasi_X₂_of_ne_e6Six c hc K hK D

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
