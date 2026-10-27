module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def Lemma313NarrowInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    solomonKStarOf (normalizer (solomonKStarOf N : Set G)) = solomonKStarOf N →
    (∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ normalizer (solomonKStarOf N : Set G)) →
    ∀ K ∈ kStarComponents N, ∀ g : G,
      K ≤ conjugate (normalizer (solomonKStarOf N : Set G)) g →
      (∀ K' ∈ kStarComponents N, ∀ s ∈ K', orderOf s = 2 → ∀ L ∈ kStarComponents N,
        ¬ conjugate L g ≤ centralizer ({s} : Set G)) →
      (∀ L ∈ kStarComponents N, ∀ s ∈ conjugate L g, orderOf s = 2 →
        ∀ K' ∈ kStarComponents N, ¬ K' ≤ centralizer ({s} : Set G)) →
      ((∃ L ∈ kStarComponents N, ¬ K ≤ normalizer (conjugate L g : Set G)) ∨
        (∃ L ∈ kStarComponents N, conjugate L g ≤ normalizer (solomonKStarOf N : Set G) ∧
          ∃ K' ∈ kStarComponents N, ¬ conjugate L g ≤ normalizer (K' : Set G)) ∨
        ∀ L ∈ kStarComponents N, K ≤ normalizer (conjugate L g : Set G) ∧
          ¬ K ≤ coreActionKernel (conjugate L g) ∧
          (K ≤ conjugate L g ⊔ coreActionKernel (conjugate L g) →
            ¬ conjugate L g ≤ K ⊔ coreActionKernel (conjugate L g))) →
      g ∈ normalizer (solomonKStarOf N : Set G)

end CFSG.ComponentClassification.Sol76
