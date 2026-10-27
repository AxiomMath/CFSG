module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34AutRankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K E : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → E ≤ normalizer (K : Set G) → IsElemTwo E →
    Nat.card E ≤ 16 * Nat.card ↥(E ⊓ coreActionKernel K)

@[expose] def L34ElementaryRankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
    (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
    ∃ A : Subgroup G, A ≤ P ∧ IsElemTwo A ∧ Nat.card A = 16 * Nat.card ↥(P ⊓ zStarIn K)

end CFSG.ComponentClassification.GrSLit
