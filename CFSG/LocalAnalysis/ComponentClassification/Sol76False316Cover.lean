module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def False316CoverFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ M : Subgroup G, M = normalizer (solomonKStarOf M : Set G) →
    (∀ K ∈ kStarComponents N, ∃ K' ∈ kStarComponents M, K ≤ K' ∧ K' ≤ K ⊔ oddCoreIn K') →
    (∀ K' ∈ kStarComponents M, ∃ K ∈ kStarComponents N, K ≤ K') →
    (∀ K' ∈ kStarComponents M, ∀ s ∈ K', orderOf s = 2 → centralizer ({s} : Set G) ≤ M) →
    False

end CFSG.ComponentClassification.Sol76
