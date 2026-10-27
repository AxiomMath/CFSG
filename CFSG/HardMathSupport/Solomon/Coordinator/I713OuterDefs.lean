module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def I_7_13_1_OuterPPrime : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ¬ p ∣ Nat.card K →
      CFSG.Open.pRank p (⊤ : Subgroup (Outer K)) ≤ 1

end CFSG.HardMathSupport.Solomon.Coordinator
