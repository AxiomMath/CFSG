module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props316

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def Lemma33CentralInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ a ∈ normalizer (solomonKStarOf N : Set G), orderOf a = 2 →
      K ≤ centralizer ({a} : Set G) →
      conjClosure K (twoLayerIn (centralizer ({a} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔ K

@[expose] def Lemma33ResidueInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ a ∈ normalizer (solomonKStarOf N : Set G), orderOf a = 2 →
      K ≤ centralizer ({a} : Set G) →
      (∀ K' ∈ kStarComponents N, K' ≠ K →
        CFSG.Open.pRank 2 (K' ⊓ centralizer ({a} : Set G)) ≤ 1) →
      conjClosure K (twoLayerIn (centralizer ({a} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔ K

theorem lemma33ResidueInput_of_thm13 (h : SolomonThm13Input) : Lemma33ResidueInputFor (fun G _ _ => Thm13Below G) :=
  
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

end CFSG.ComponentClassification.Sol76
