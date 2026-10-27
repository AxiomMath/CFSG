module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props316

public section

namespace CFSG.ComponentClassification.Sol76

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

@[expose] def Lemma315bInputFor (𝒜 : Thm13Ambient) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 𝒜 G → ∀ N : Subgroup G, IsSolomonChoice N →
    ∀ K ∈ kStarComponents N, ∀ K' ∈ kStarComponents N, K ≠ K' →
    ∀ B : Subgroup G, B ≤ K → CFSG.Open.IsElemAbelian 2 B → 4 ≤ Nat.card B →
    ∀ V : Subgroup G, V ≤ twoLayerIn (K' ⊓ centralizer (B : Set G)) →
      CFSG.Open.IsElemAbelian 2 V → V ≠ ⊥ →
    ∀ e ∈ B, e ≠ 1 →
      ⁅oddCoreIn (centralizer ({e} : Set G)), V⁆ = ⊥ ∧
        oddCoreIn (centralizer ({e} : Set G)) ⊓ oddCoreIn (centralizer (V : Set G)) = ⊥

theorem lemma315bInput_of_thm13 (h : SolomonThm13Input) : Lemma315bInputFor (fun G _ _ => Thm13Below G) :=
  
  fun _ _ _ _ _ hN => (not_isSolomonChoice_of_thm13 h hN).elim

end CFSG.ComponentClassification.Sol76
