module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def False316For (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N →
    (∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) → False

end CFSG.ComponentClassification.Sol76
