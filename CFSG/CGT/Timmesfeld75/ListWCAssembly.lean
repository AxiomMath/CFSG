module

public import CFSG.CGT.Timmesfeld75.ListWCL2
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.CGT.Timmesfeld75.ListWCAlt
public import CFSG.CGT.Timmesfeld75.ListWCAlt9

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem WCOrderConj.of_mulEquiv {G M : Type} [Group G] [Group M] {n : ℕ} (h : WCOrderConj M n)
    (e : G ≃* M) : WCOrderConj G n := by
  intro T hT h4
  have hcard : Nat.card (T.map e.toMonoidHom) = Nat.card T :=
    Subgroup.card_map_of_injective e.injective
  obtain ⟨hc, hconj⟩ := h (T.map e.toMonoidHom) (hT.map_mulEquiv e) (hcard ▸ h4)
  exact ⟨hcard ▸ hc, isConj_of_map_mulEquiv e hconj⟩

theorem wcOrderConj_of_mathieu {G : Type} [Group G] (hM : WCOrderConj
    CFSG.Blueprint.NativeSporadic.M22 16 ∧ WCOrderConj CFSG.Blueprint.NativeSporadic.M23 16 ∧
    WCOrderConj CFSG.Blueprint.NativeSporadic.M24 16)
    (hG : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M24) : WCOrderConj G 16 := by
  rcases hG with h | h | h
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M22) := h
    exact hM.1.of_mulEquiv e
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M23) := h
    exact hM.2.1.of_mulEquiv e
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.M24) := h
    exact hM.2.2.of_mulEquiv e

theorem listWCIdentification_of_mathieu (hM : WCOrderConj CFSG.Blueprint.NativeSporadic.M22 16 ∧
    WCOrderConj CFSG.Blueprint.NativeSporadic.M23 16 ∧ WCOrderConj CFSG.Blueprint.NativeSporadic.M24
    16) :
    ListWCIdentification := by
  intro Λ _ _ _ hL S hS h4
  have hS1 : S ≠ ⊥ := ne_bot_of_four_le_card h4
  have htr : ∀ x ∈ S, x ≠ 1 → ∀ y ∈ S, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (S : Set Λ), g * x * g⁻¹ = y := by
    rcases hL with ⟨m, s, hm, -, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, -, -, hmod⟩ |
      ⟨k, hk6, hk9, ⟨e⟩⟩ | h22 | h23 | h24
    · rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
      · exact (psl2_wc hmod hS hS1).2
      · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
        have : CharP K 2 := charP_two_of_card hK
        exact hS.transitive_of_isConj (lin_wc hm3 e hS hS1).2.2
    · exact (psu3_wc hs hmod hS hS1).2
    · exact (sz_wc hmod hS hS1).2
    · rcases (show k ≤ 7 ∨ k = 8 ∨ k = 9 by omega) with hk7 | rfl | rfl
      · exact (alt67_wc hk6 hk7 e hS h4).2
      · exact hS.transitive_of_isConj (alt8_wc e hS hS1).2
      · exact hS.transitive_of_isConj (alt9_wc e hS hS1).2
    · exact hS.transitive_of_isConj (wcOrderConj_of_mathieu hM (Or.inl h22) S hS h4).2
    · exact hS.transitive_of_isConj
        (wcOrderConj_of_mathieu hM (Or.inr (Or.inl h23)) S hS h4).2
    · exact hS.transitive_of_isConj
        (wcOrderConj_of_mathieu hM (Or.inr (Or.inr h24)) S hS h4).2
  refine ⟨hL, htr, fun f hf => (psl2_wc hf hS hS1).1, ?_, fun s _ _ hmod => (sz_wc hmod hS hS1).1,
    fun s hs hmod => (psu3_wc hs hmod hS hS1).1, ?_,
    fun h => (wcOrderConj_of_mathieu hM h S hS h4).1⟩
  · intro m f hm K hF hFin hK e
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨hcard, hid, -⟩ := lin_wc hm e hS hS1
    exact ⟨by rw [hcard, hK, ← pow_mul], hid⟩
  · rintro k hk6 hk9 ⟨e⟩
    rcases (show k ≤ 7 ∨ k = 8 ∨ k = 9 by omega) with hk7 | rfl | rfl
    · simp only [hk7, ↓reduceIte]
      exact (alt67_wc hk6 hk7 e hS h4).1
    · exact (alt8_wc e hS hS1).1
    · exact (alt9_wc e hS hS1).1

end CFSG.CGT.Timmesfeld75
