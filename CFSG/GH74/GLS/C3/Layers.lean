module

public import CFSG.GH74.GLS.C3.Layer2.Config
public import CFSG.GH74.GLS.C3.Layer3.OrderStep

public section

namespace CFSG.GH74.GLS

@[expose] def S_layerI : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∃ n ∈ ({5, 6, 7} : Finset ℕ), AConfig G n

@[expose] def S_prop121_cfg : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 → ∀ n ∈ ({5, 6, 7} : Finset ℕ),
    AConfig G n → IsApproxTo G (alternatingGroup (Fin (n + 4))) →
      ∃ G₀ : Subgroup G, Nonempty (G₀ ≃* alternatingGroup (Fin (n + 4)))

theorem S_C3_gen4_of_layers (h1 : S_layerI) (h2 : S_layerII) (h3 : S_prop121_cfg) :
    S_C3_gen4 := by
  intro G _ _ hG
  obtain ⟨n, hn, hcfg⟩ := h1 G hG
  have hA := h2 G hG n hn hcfg
  obtain ⟨G₀, ⟨e⟩⟩ := h3 G hG.gen4.pRank_two_le n hn hcfg hA
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  obtain ⟨e'⟩ := Layer3.nonempty_mulEquiv_of_subgroup_alt (n := n + 4) (by omega) (by omega) hA.1 G₀ e
  rcases hn' with rfl | rfl | rfl
  · exact Or.inl ⟨e'⟩
  · exact Or.inr (Or.inl ⟨e'⟩)
  · exact Or.inr (Or.inr ⟨e'⟩)

end CFSG.GH74.GLS
