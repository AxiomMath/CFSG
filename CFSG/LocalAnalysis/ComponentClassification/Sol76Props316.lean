module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def Lemma32InputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ b ∈ K, orderOf b = 2 → K' ≤ centralizer ({b} : Set G) →
      conjClosure (twoLayerIn (K' ⊓ centralizer ({b} : Set G)))
          (twoLayerIn (centralizer ({b} : Set G))) ≤
        oddCoreIn (twoLayerIn (centralizer ({b} : Set G))) ⊔
          twoLayerIn (K' ⊓ centralizer ({b} : Set G))

@[expose] def Lemma32Input : Prop := Lemma32InputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma315aInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    oddCoreIn (solomonKStarOf N) ≤ centralizer (solomonKStarOf N : Set G)

@[expose] def Lemma315aInput : Prop := Lemma315aInputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma315cInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ b ∈ K, orderOf b = 2 →
      oddCoreIn (solomonKStarOf (centralizer ({b} : Set G))) ≤
        centralizer (solomonKStarOf (centralizer ({b} : Set G)) : Set G)

@[expose] def Lemma315cInput : Prop := Lemma315cInputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma316BalancedInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ 𝒮 : Set (Subgroup G), 𝒮 ⊆ kStarComponents N → 𝒮.Nonempty →
      kStarComponents (normalizer ((sSup 𝒮 : Subgroup G) : Set G)) = kStarComponents N

@[expose] def Lemma316BalancedInput : Prop := Lemma316BalancedInputFor (fun G _ _ => Thm13Below G)

@[expose] def Lemma316ProductInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ b ∈ K, orderOf b = 2 →
      ∀ J : Subgroup G, IsTwoComponentIn J (centralizer ({b} : Set G)) → J ∈ solomonKStar G →
        J ≤ twoLayerIn (normalizer (solomonKStarOf N : Set G)) → J ∈ kStarComponents N

@[expose] def Lemma316ProductInput : Prop := Lemma316ProductInputFor (fun G _ _ => Thm13Below G)

theorem not_isSolomonChoice_of_thm13 (h : SolomonThm13Input) {G : Type} [Group G] [Finite G]
    {N : Subgroup G} (hN : IsSolomonChoice N) : False :=
  hN.2.1 (h G N hN.1)

theorem lemma32Input_of_thm13 (h : SolomonThm13Input) : Lemma32Input :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

theorem lemma315aInput_of_thm13 (h : SolomonThm13Input) : Lemma315aInput :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

theorem lemma315cInput_of_thm13 (h : SolomonThm13Input) : Lemma315cInput :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

theorem lemma316BalancedInput_of_thm13 (h : SolomonThm13Input) : Lemma316BalancedInput :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

theorem lemma316ProductInput_of_thm13 (h : SolomonThm13Input) : Lemma316ProductInput :=
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

end CFSG.ComponentClassification.Sol76
