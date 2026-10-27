module

public import CFSG.LargeExtraspecial.GLRLinGL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

omit [Finite G] in
theorem finrank_span_le_two (a b : S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({a, b} : Set S.Qt)) ≤ 2 := by
  classical
  have := finrank_span_finset_le_card (R := ZMod 2) ({a, b} : Finset S.Qt)
  rw [Finset.coe_insert, Finset.coe_singleton] at this
  exact this.trans Finset.card_le_two

omit [Finite G] in
theorem finrank_span_le_three (a b c : S.Qt) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({a, b, c} : Set S.Qt)) ≤ 3 := by
  classical
  have := finrank_span_finset_le_card (R := ZMod 2) ({a, b, c} : Finset S.Qt)
  rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton] at this
  exact this.trans Finset.card_le_three

namespace Pair

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt}

theorem exists_mem_A_notMem (h : Pair S X A B) {U : Submodule (ZMod 2) S.Qt}
    (hU : finrank (ZMod 2) U < S.width) : ∃ a ∈ A, a ∉ U := by
  by_contra hc
  push Not at hc
  have := Submodule.finrank_mono (show A ≤ U from hc)
  rw [h.finrank_A] at this
  omega

theorem exists_apply_eq_of_ne_zero (h : Pair S X A B) {a a' : S.Qt} (ha : a ∈ A) (ha' : a' ∈ A)
    (ha0 : a ≠ 0) (ha'0 : a' ≠ 0) : ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a' := by
  by_cases e : a = a'
  · exact ⟨1, X.one_mem, by rw [e]; rfl⟩
  have hnot : a ∉ Submodule.span (ZMod 2) ({a + a'} : Set S.Qt) := by
    intro hm
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hm
    rcases zmod2_eq_zero_or_one t with rfl | rfl
    · rw [zero_smul] at ht
      exact ha0 ht.symm
    · rw [one_smul] at ht
      exact ha'0 (by simpa using ht)
  have hsp : Submodule.span (ZMod 2) ({a + a'} : Set S.Qt) ≤ A :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (A.add_mem ha ha')
  obtain ⟨c, -, hc0, hc1⟩ := h.exists_polar_sep hsp ha hnot
  have hu : polar S.q (a + a') c = 0 := hc0 _ (Submodule.mem_span_singleton_self _)
  obtain ⟨x, hx, hxa⟩ := h.exists_transvection (A.add_mem ha ha') hu
  refine ⟨x, hx, ?_⟩
  rw [hxa a ha, hc1, one_smul, ← add_assoc, two_vec, zero_add]

theorem eq_bot_or_eq_A (h : Pair S X A B) {W : Submodule (ZMod 2) S.Qt} (hWA : W ≤ A)
    (hW : ∀ x ∈ X, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) : W = ⊥ ∨ W = A := by
  by_cases hb : W = ⊥
  · exact Or.inl hb
  refine Or.inr (le_antisymm hWA fun a ha => ?_)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  by_cases ha0 : a = 0
  · rw [ha0]; exact W.zero_mem
  obtain ⟨x, hx, rfl⟩ := h.exists_apply_eq_of_ne_zero (hWA hw) ha hw0 ha0
  exact hW x hx w hw

theorem exists_fix_move (h : Pair S X A B) (hn : 3 ≤ S.width) {a b : S.Qt} (ha : a ∈ A)
    (hb : b ∈ B) (hb0 : b ≠ 0) :
    ∃ x ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a ∧ (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b ≠ b := by
  obtain ⟨u, hu, hub⟩ := h.exists_polar_eq_one hb hb0
  have hsp : Submodule.span (ZMod 2) ({a, u} : Set S.Qt) ≤ A := by
    rw [Submodule.span_le]
    rintro v (rfl | rfl)
    exacts [ha, hu]
  obtain ⟨a'', ha'', ha''U⟩ := h.exists_mem_A_notMem (U := Submodule.span (ZMod 2) {a, u})
    ((finrank_span_le_two a u).trans_lt (by omega))
  obtain ⟨c, hc, hcU, hc1⟩ := h.exists_polar_sep hsp ha'' ha''U
  have hac : polar S.q a c = 0 := hcU a (Submodule.subset_span (by simp))
  have huc : polar S.q u c = 0 := hcU u (Submodule.subset_span (by simp))
  obtain ⟨x, hx, hxa⟩ := h.exists_transvection hu huc
  refine ⟨x, hx, by rw [hxa a ha, hac, zero_smul, add_zero], fun hxb => ?_⟩
  have := ((h.apply_eq_self_iff hx hb).mp hxb) a'' ha''
  rw [hxa a'' ha'', hc1, one_smul, polar_add_left, hub] at this
  have h2 : polar S.q a'' b + 1 - polar S.q a'' b = 0 := by rw [this, sub_self]
  rw [add_sub_cancel_left] at h2
  exact one_ne_zero h2

theorem invariant (h : Pair S X A B) (hn : 3 ≤ S.width) (W : Submodule (ZMod 2) S.Qt)
    (hW : ∀ x ∈ X, ∀ v ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ W) :
    W = ⊥ ∨ W = A ∨ W = B ∨ W = ⊤ := by
  have hWA := h.eq_bot_or_eq_A (W := W ⊓ A) inf_le_right
    fun x hx v hv => ⟨hW x hx v hv.1, h.apply_A x hx v hv.2⟩
  have hWB := h.symm.eq_bot_or_eq_A (W := W ⊓ B) inf_le_right
    fun x hx v hv => ⟨hW x hx v hv.1, h.apply_B x hx v hv.2⟩
  have hdec : ∀ w ∈ W, ∃ a ∈ A, ∃ b ∈ B, a + b = w := fun w _ => by
    have hv : w ∈ A ⊔ B := by rw [h.sup_eq]; exact Submodule.mem_top
    exact Submodule.mem_sup.mp hv
  have hle : ∀ {U : Submodule (ZMod 2) S.Qt}, W ⊓ U = U → U ≤ W := fun hU => by
    rw [← hU]; exact inf_le_left
  rcases hWA with hA | hA <;> rcases hWB with hB | hB
  ·
    left
    by_contra hW0
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w hw
    have hb0 : b ≠ 0 := by
      rintro rfl
      have : a + 0 ∈ W ⊓ A := ⟨hw, by rw [add_zero]; exact ha⟩
      rw [hA, Submodule.mem_bot] at this
      exact hw0 this
    obtain ⟨x, hx, hxa, hxb⟩ := h.exists_fix_move hn ha hb hb0
    have hd : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b ∈ W ⊓ B := by
      refine ⟨?_, B.sub_mem (h.apply_B x hx b hb) hb⟩
      have e : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b =
          (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (a + b) - (a + b) := by
        rw [map_add, hxa]; abel
      rw [e]
      exact W.sub_mem (hW x hx _ hw) hw
    rw [hB, Submodule.mem_bot, sub_eq_zero] at hd
    exact hxb hd
  ·
    right; right; left
    refine le_antisymm (fun w hw => ?_) (hle hB)
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w hw
    have hbW : b ∈ W := hle hB hb
    have haW : a ∈ W ⊓ A := ⟨by simpa using W.sub_mem hw hbW, ha⟩
    rw [hA, Submodule.mem_bot] at haW
    rw [haW, zero_add]
    exact hb
  ·
    right; left
    refine le_antisymm (fun w hw => ?_) (hle hA)
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec w hw
    have haW : a ∈ W := hle hA ha
    have hbW : b ∈ W ⊓ B := ⟨by simpa using W.sub_mem hw haW, hb⟩
    rw [hB, Submodule.mem_bot] at hbW
    rw [hbW, add_zero]
    exact ha
  ·
    right; right; right
    refine eq_top_iff.mpr ?_
    rw [← h.sup_eq]
    exact sup_le (hle hA) (hle hB)

end Pair

end CFSG.LargeExtraspecial.GLR
