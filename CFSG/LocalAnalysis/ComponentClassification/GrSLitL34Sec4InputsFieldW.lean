module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34OuterWitnessFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G) (b : G), ⁅J, J⁆ = J →
    IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J → b ∈ normalizer (J : Set G) →
    b ∈ normalizer (P : Set G) → b * b = 1 → b ∉ withKernel J →
    ∃ w ∈ P, w * w = 1 ∧ w * b = b * w ∧ w ∉ zStarIn J

end CFSG.ComponentClassification.GrSLit
