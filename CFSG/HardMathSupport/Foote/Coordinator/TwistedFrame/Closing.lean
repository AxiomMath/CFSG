module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.TheoremA
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.PureA
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredF4Aux8
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux5
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingF4Even
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TwelveTwo

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


theorem TwClass.minQ_le_three (c : TwClass) : c.minQ ≤ 3 := by
  cases c <;> simp [TwClass.minQ]

theorem twPure (c : TwClass) (K : Type) [Field K] [Finite K] (hK : c.minQ ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) : TwPure (c.X₁ D) (c.X₂ D) := by
  by_cases hc : c = TwClass.e8Twelve
  · subst hc
    exact twPure_D4 K hK D
  · exact twPure_A c hc K hK D


theorem twFrameCore (c : TwClass) (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) (hQ : TwQuasi (c.X₁ D) (c.X₂ D)) : TwFrameCore (c.X₁ D) (c.X₂ D) :=
  have hK : c.minQ ≤ Nat.card K := c.minQ_le_three.trans h3
  { basic := twBasic c K hK D
    quasi := hQ
    central := twCentral c K hK D
    coords := twCoords c K hK D
    pure := twPure c K hK D
    three_le := h3 }

theorem twClosing_of_irred (c : TwClass) (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi c.tag K c.w) (hQ : TwQuasi (c.X₁ D) (c.X₂ D)) (hI : TwIrred (c.X₁ D) (c.X₂ D)) :
    TwFrameClosing c.tag K (c.X₁ D ⊔ c.X₂ D) :=
  theoremA { toTwFrameCore := twFrameCore c K h3 D hQ, irred := hI }

theorem twClosing_f4Six (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.f4Six.tag K TwClass.f4Six.w) :
    TwFrameClosing TwClass.f4Six.tag K (TwClass.f4Six.X₁ D ⊔ TwClass.f4Six.X₂ D) := by
  by_cases h2 : ringChar K = 2
  · haveI : CharP K 2 := ringChar.of_eq h2
    have h4 : 4 ≤ Nat.card K := by
      have : Fintype K := Fintype.ofFinite K
      obtain ⟨n, hn, hcard⟩ := FiniteField.card K 2
      rw [Nat.card_eq_fintype_card, hcard]
      rw [Nat.card_eq_fintype_card, hcard] at h3
      have hn1 : 2 ≤ (n : ℕ) := by
        by_contra hlt
        have hn0 := n.pos
        have h1 : (n : ℕ) = 1 := by omega
        rw [h1] at h3
        norm_num at h3
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn1
    exact twClosing_f4Six_even K h4 D
  · exact twClosing_of_irred TwClass.f4Six K h3 D
      (twQuasi_of_ne_e6Six TwClass.f4Six (by decide) K h3 D) (IrredF4Aux.main h3 h2 D)

section E6Sc


theorem twClosing_e6Six (K : Type) [Field K] [Finite K] (h3 : 3 ≤ Nat.card K)
    (D : LangLevi TwClass.e6Six.tag K TwClass.e6Six.w) :
    TwFrameClosing TwClass.e6Six.tag K (TwClass.e6Six.X₁ D ⊔ TwClass.e6Six.X₂ D) :=
  twClosing_of_irred TwClass.e6Six K h3 D (twQuasi TwClass.e6Six K h3 D) (
      IrredE6Aux.twIrred_core h3 D)

end E6Sc

theorem twClosing_e8Twelve (K : Type) [Field K] [Finite K]
    (D : LangLevi TwClass.e8Twelve.tag K TwClass.e8Twelve.w) :
    TwFrameClosing TwClass.e8Twelve.tag K (TwClass.e8Twelve.X₁ D ⊔ TwClass.e8Twelve.X₂ D) := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  by_cases h3 : 3 ≤ Nat.card K
  · exact twClosing_of_irred TwClass.e8Twelve K h3 D
      (twQuasi_of_ne_e6Six TwClass.e8Twelve (by decide) K h2 D) (twIrred_e8Twelve K h2 D)
  · exact twClosing_e8Twelve_two K (by omega) D

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
