module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34AutRankOneNormalFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S D : Subgroup G), ⁅L, L⁆ = L →
    IsL34Type (L ⧸ Open.fusionZStar L) → IsSylowTwoIn S (normalizer (L : Set G)) → D ≤ S →
    S ≤ normalizer (D : Set G) → D ⊓ coreActionKernel L = ⊥ →
    (∀ d ∈ D, ∀ e ∈ D, d * d = 1 → e * e = 1 → d = 1 ∨ e = 1 ∨ d = e) →
    Nat.card D ≤ 2

end CFSG.ComponentClassification.GrSLit
