module

public import CFSG.GH74.GLS.C3.Layer1.BkL113aSix

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1.Back

@[expose] def B_lemma113a_rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K L M T Q : Subgroup G),
    Hyp9 x K L M T Q → Prop91Concl K M T Q → ¬ HasL2Model (kBar K) (fun r => r = 7) →
    IsSylowOf 2 T ⊤ →
    (Nonempty (kBar K ≃* alternatingGroup (Fin 5)) ∨
      (Nonempty (kBar K ≃* alternatingGroup (Fin 7)) ∧ K ≠ L)) → False

theorem b_lemma113a_of_rest
    (h112 : S_lemma112) (hrest : B_lemma113a_rest) :
    B_lemma113a := by
  intro G _ _ hG x K L M T Q hh p91 hK7 hT
  obtain ⟨n, hn, ⟨e⟩⟩ := kbar_alt p91 hK7
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact hrest G hG x K L M T Q hh p91 hK7 hT (Or.inl ⟨e⟩)
  ·
    have hKL : K = L := by
      rcases hh.b with hB1 | hB2
      · exfalso
        obtain ⟨y, hy⟩ := hB1.v2star
        have hex : ∃ (x' y' : G) (K' : Subgroup G), IsV2Triple x' y' K' := ⟨x, y, K, hy.1.1.1.1⟩
        have h360 : Nat.card (kBar K) = 360 := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
          simp [Nat.factorial]
        rcases p91.2.2.2 hex with h5 | h7
        · have := card_eq_of_hasL2Model_five h5
          omega
        · obtain ⟨e7⟩ := h7
          have h2520 : Nat.card (kBar K) = 2520 := by
            rw [Nat.card_congr e7.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
            simp [Nat.factorial]
          omega
      · exact hh.a.terminal_eq hB2.terminal
    subst hKL
    exact lemma113a_alt67 h112 hG hh p91 (Or.inl ⟨e⟩) hT
  · by_cases hKL : K = L
    · subst hKL
      exact lemma113a_alt67 h112 hG hh p91 (Or.inr ⟨e⟩) hT
    · exact hrest G hG x K L M T Q hh p91 hK7 hT (Or.inr ⟨⟨e⟩, hKL⟩)

end CFSG.GH74.GLS.C3.Layer1.Bk
