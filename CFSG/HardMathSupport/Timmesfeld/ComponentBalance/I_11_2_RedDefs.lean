module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Defs

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def I112Red : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ p : ℕ, p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ → ∀ B : Subgroup X, IsElemAbelian p B →
      GLATwoLocalRank p X ≤ CFSG.Open.pRank p B → ∀ L : Subgroup X, GLAPComponent p ⊤ L →
        ¬ B ≤ Subgroup.normalizer (L : Set X) →
          p = 3 ∧ (Subgroup.normalizer (L : Set X)).relIndex B = 3 ∧
            (Subgroup.center ↥L ≠ ⊥ ∨ IsL2TwoPowOdd ↥L)

structure TableL2 : Prop where
  T : ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → CFSG.Open.IsKGroup L →
    Nat.card (Subgroup.center L) = 1 → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 →
      GLATwoLocalRank 3 L = 0 → IsL2TwoPowOdd L

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
