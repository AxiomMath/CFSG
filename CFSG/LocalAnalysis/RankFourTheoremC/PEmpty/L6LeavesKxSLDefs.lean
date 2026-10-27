module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

@[expose] def KFactSporLocal : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L K₀ : Subgroup A) (s : TauCeti.SporadicName) (z : A)
    (p : ℕ),
    Nonempty (↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group) → 2 ≤ CFSG.Open.pRank 3 L →
    (∀ U : Subgroup A, U ≤ L → U ≠ ⊥ → IsPGroup 2 U →
      CFSG.Open.pRank 3 (normalizer (U : Set A) ⊓ L) ≤ 3) →
    p.Prime → 5 ≤ p → CFSG.Open.pRank p L ≤ 1 → orderOf z = p →
    K₀ ≤ L → z ∈ K₀ → ¬ L ≤ K₀ →
    normalizer (zpowers z : Set A) ⊓ L ≤ K₀ →
    (∀ U : Subgroup A, U ≤ L → IsPGroup 2 U → z ∈ normalizer (U : Set A) → U ⊓ K₀ ≠ ⊥ →
      normalizer (U : Set A) ⊓ L ≤ K₀) →
    (∃ y ∈ pCoreOf 2 K₀, z * y ≠ y * z) →
    normalizer ((pCoreOf 2 K₀ : Subgroup A) : Set A) ⊓ L = K₀ →
    KxSection z K₀ 3 ∧ s ≠ .M11

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
