module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props316

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def Lemma33InputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ a ∈ normalizer (solomonKStarOf N : Set G), orderOf a = 2 →
      (∀ k ∈ K, a⁻¹ * k⁻¹ * a * k ∈ oddCoreIn (solomonKStarOf N)) →
      conjClosure (twoLayerIn (K ⊓ centralizer ({a} : Set G)))
          (twoLayerIn (centralizer ({a} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔
          twoLayerIn (K ⊓ centralizer ({a} : Set G))

@[expose] def Lemma33Input : Prop := Lemma33InputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma313ResidueInputFor (𝒜 : Thm13Ambient) : Prop :=
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
      g ∈ normalizer (solomonKStarOf N : Set G)

@[expose] def Lemma313ResidueInput : Prop := Lemma313ResidueInputFor (fun G _ _ => Thm13Below G)

theorem lemma33Input_of_thm13 (h : SolomonThm13Input) : Lemma33Input :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

theorem lemma313ResidueInput_of_thm13 (h : SolomonThm13Input) : Lemma313ResidueInput :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

end CFSG.ComponentClassification.Sol76
