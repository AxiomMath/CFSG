module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxSLDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

@[expose] def KFactSporLocalRow (s : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L K₀ : Subgroup A) (z : A),
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

theorem kFactSporLocal_iff_rows :
    KFactSporLocal ↔ ∀ (s : TauCeti.SporadicName) (p : ℕ), KFactSporLocalRow s p :=
  ⟨fun h s p A _ _ L K₀ z => h A L K₀ s z p, fun h A _ _ L K₀ s z p => h s p A L K₀ z⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
