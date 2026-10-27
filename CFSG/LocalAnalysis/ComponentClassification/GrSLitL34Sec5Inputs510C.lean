module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34SylowCentralLiftFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K S : Subgroup G), ⁅K, K⁆ = K →
    IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn S (normalizer (K : Set G)) →
    (∀ z ∈ S ⊓ zStarIn K, z * z = 1) →
    ∃ y ∈ S ⊓ K, y ∉ zStarIn K ∧ y * y = 1 ∧ ∀ s ∈ S, s * y = y * s

end CFSG.ComponentClassification.GrSLit
