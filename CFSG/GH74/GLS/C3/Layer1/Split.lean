module

public import CFSG.GH74.GLS.C3.Layers
public import CFSG.GH74.GLS.C3.Layer1.Defs

public section

namespace CFSG.GH74.GLS

@[expose] def S_back : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → ∃ n ∈ ({5, 6, 7} : Finset ℕ), AConfig G n

@[expose] def S_front : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    ∃ (x : G) (K L M T Q : Subgroup G), Hyp9 x K L M T Q

theorem s_layerI_of (hF : S_front) (hB : S_back) : S_layerI := by
  intro G _ _ hG
  obtain ⟨x, K, L, M, T, Q, h⟩ := hF G hG
  exact hB G hG x K L M T Q h

@[expose] def S_stage1_rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    IsEvenType G ∨ ∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K

@[expose] def S_thm1_rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    (∃ (x y : G) (K : Subgroup G), Is2TerminalU2Triple x y K) →
      ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K

@[expose] def S_thm2_rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    (∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
      ∃ (x : G) (K L M T Q : Subgroup G), Hyp9A x K L M T Q ∧ Hyp9B1 x K T Q

@[expose] def S_evenSetup_rank4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
      ∃ (x : G) (K L M T Q : Subgroup G), Hyp9A x K L M T Q ∧ Hyp9B2 x K M T Q

theorem s_front_of (h1 : S_stage1_rank4) (h2 : S_thm1_rank4) (h3 : S_thm2_rank4)
    (h4 : S_evenSetup_rank4) : S_front := by
  intro G _ _ hG
  by_cases hV : ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K
  · obtain ⟨x, K, L, M, T, Q, ha, hb⟩ := h3 G hG hV
    exact ⟨x, K, L, M, T, Q, ⟨ha, Or.inl hb⟩⟩
  · have hE : IsEvenType G := by
      rcases h1 G hG with he | hU
      · exact he
      · exact absurd (h2 G hG hU) hV
    obtain ⟨x, K, L, M, T, Q, ha, hb⟩ := h4 G hG hE hV
    exact ⟨x, K, L, M, T, Q, ⟨ha, Or.inr hb⟩⟩

theorem s_layerI_of_parts (h1 : S_stage1_rank4) (h2 : S_thm1_rank4) (h3 : S_thm2_rank4)
    (h4 : S_evenSetup_rank4) (hB : S_back) : S_layerI :=
  s_layerI_of (s_front_of h1 h2 h3 h4) hB

end CFSG.GH74.GLS
