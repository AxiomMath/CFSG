module

public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.Timmesfeld75

open scoped MatrixGroups
open CFSG.Open

section Matrix

variable {F : Type} [Field F]

@[expose] def sl2Mk (a b c d : F) (h : a * d - b * c = 1) : SL(2, F) :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem sl2Mk_apply_00 (a b c d : F) (h : a * d - b * c = 1) : sl2Mk a b c d h 0 0 = a := by
  simp [sl2Mk]

theorem sl2Mk_apply_01 (a b c d : F) (h : a * d - b * c = 1) : sl2Mk a b c d h 0 1 = b := by
  simp [sl2Mk]

theorem sl2Mk_apply_10 (a b c d : F) (h : a * d - b * c = 1) : sl2Mk a b c d h 1 0 = c := by
  simp [sl2Mk]

theorem sl2Mk_apply_11 (a b c d : F) (h : a * d - b * c = 1) : sl2Mk a b c d h 1 1 = d := by
  simp [sl2Mk]

variable [CharP F 2]

theorem mul_self_eq_one_of_trace_eq_zero {g : SL(2, F)} (h : g 0 0 + g 1 1 = 0) : g * g = 1 := by
  have hD := sl2_det g
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  apply sl2_ext
  all_goals sl2_simp
  · linear_combination (-1 : F) * hD + g 0 0 * h - h2
  · linear_combination g 0 1 * h
  · linear_combination g 1 0 * h
  · linear_combination (-1 : F) * hD + g 1 1 * h - h2

theorem exists_mul_self_eq_one_mul_self_eq_one (x : SL(2, F)) :
    ∃ a : SL(2, F), a * a = 1 ∧ (a * x) * (a * x) = 1 := by
  have hD := sl2_det x
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  by_cases hr : x 1 0 = 0
  · by_cases hq : x 0 1 = 0
    · have hps : x 0 0 * x 1 1 = 1 := by
        rw [hr, hq] at hD
        linear_combination hD
      refine ⟨sl2Mk 0 (x 0 0) (x 1 1) 0 (by linear_combination (-1 : F) * hps - h2),
        mul_self_eq_one_of_trace_eq_zero ?_, mul_self_eq_one_of_trace_eq_zero ?_⟩
      · simp only [sl2Mk_apply_00, sl2Mk_apply_11, add_zero]
      · simp only [mul_apply_00, mul_apply_11, sl2Mk_apply_00, sl2Mk_apply_01, sl2Mk_apply_10,
          sl2Mk_apply_11]
        rw [hr, hq]
        ring
    · obtain ⟨γ, hγ⟩ : ∃ γ : F, γ * x 0 1 = x 1 1 ^ 2 + 1 := ⟨_, div_mul_cancel₀ _ hq⟩
      refine ⟨sl2Mk (x 1 1) (x 0 1) γ (x 1 1) (by linear_combination (-1 : F) * hγ - h2),
        mul_self_eq_one_of_trace_eq_zero ?_, mul_self_eq_one_of_trace_eq_zero ?_⟩
      · simp only [sl2Mk_apply_00, sl2Mk_apply_11]
        linear_combination x 1 1 * h2
      · simp only [mul_apply_00, mul_apply_11, sl2Mk_apply_00, sl2Mk_apply_01, sl2Mk_apply_10,
          sl2Mk_apply_11]
        linear_combination hD + hγ + (x 0 1 * x 1 0 + 1 + x 1 1 ^ 2) * h2
  · obtain ⟨β, hβ⟩ : ∃ β : F, β * x 1 0 = x 0 0 ^ 2 + 1 := ⟨_, div_mul_cancel₀ _ hr⟩
    refine ⟨sl2Mk (x 0 0) β (x 1 0) (x 0 0) (by linear_combination (-1 : F) * hβ - h2),
      mul_self_eq_one_of_trace_eq_zero ?_, mul_self_eq_one_of_trace_eq_zero ?_⟩
    · simp only [sl2Mk_apply_00, sl2Mk_apply_11]
      linear_combination x 0 0 * h2
    · simp only [mul_apply_00, mul_apply_11, sl2Mk_apply_00, sl2Mk_apply_01, sl2Mk_apply_10,
        sl2Mk_apply_11]
      linear_combination hβ + hD + (x 0 0 ^ 2 + x 0 1 * x 1 0 + 1) * h2

theorem exists_mul_self_eq_one_conj_eq_inv (x : SL(2, F)) :
    ∃ a : SL(2, F), a * a = 1 ∧ a * x * a = x⁻¹ := by
  obtain ⟨a, ha, hax⟩ := exists_mul_self_eq_one_mul_self_eq_one x
  refine ⟨a, ha, eq_inv_of_mul_eq_one_left ?_⟩
  simpa only [mul_assoc] using hax

end Matrix

section TwoGroups

variable {G : Type*} [Group G]

theorem exists_orderOf_eq_two_pow_of_mem {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy : y ∈ P) : ∃ k : ℕ, orderOf y = 2 ^ k := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨y, hy⟩
  exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

theorem eq_one_of_odd_orderOf_map {H K : Type*} [Group H] [Group K] (f : H →* K) {P : Subgroup H}
    (hP : IsPGroup 2 P) {y : H} (hy : y ∈ P) (hodd : Odd (orderOf (f y))) : f y = 1 := by
  obtain ⟨k, hk⟩ := exists_orderOf_eq_two_pow_of_mem hP hy
  have hdvd : orderOf (f y) ∣ 2 ^ k := hk ▸ orderOf_map_dvd f y
  have hcop : Nat.Coprime (orderOf (f y)) (2 ^ k) := (Nat.coprime_two_right.2 hodd).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem eq_one_of_mul_self_eq_one_of_odd {y : G} (hy : y * y = 1) (hodd : Odd (orderOf y)) :
    y = 1 := by
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 hodd) hdvd)

theorem not_exists_isPGroup_two_mem_of_odd_orderOf {x a b : G} (hx : x = a * b)
    (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) :
    ¬ ∃ P : Subgroup G, IsPGroup 2 P ∧ a ∈ P ∧ b ∈ P := by
  rintro ⟨P, hP, ha, hb⟩
  have h1 := eq_one_of_odd_orderOf_map (MonoidHom.id G) hP (P.mul_mem ha hb)
    (by rwa [MonoidHom.id_apply, ← hx])
  exact hx1 (hx.trans h1)

end TwoGroups

namespace IsL2Pair

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem exists_involution_conj_eq_inv (h : IsL2Pair X S q) (x : X) :
    ∃ a : X, a * a = 1 ∧ a * x * a = x⁻¹ := by
  obtain ⟨F, _, _, _, e, -, -, -, -, -⟩ := h.exists_data
  obtain ⟨a, ha, hax⟩ := exists_mul_self_eq_one_conj_eq_inv (e x)
  refine ⟨e.symm a, e.injective ?_, e.injective ?_⟩
  · rw [map_mul, MulEquiv.apply_symm_apply, ha, map_one]
  · rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hax, map_inv]

theorem exists_involutions_mul_eq (h : IsL2Pair X S q) (x : X) :
    ∃ a b : X, a * a = 1 ∧ b * b = 1 ∧ x = a * b := by
  obtain ⟨a, ha, hax⟩ := h.exists_involution_conj_eq_inv x
  refine ⟨a, a * x, ha, ?_, ?_⟩
  · calc a * x * (a * x) = (a * x * a) * x := by simp only [mul_assoc]
      _ = 1 := by rw [hax, inv_mul_cancel]
  · rw [← mul_assoc, ha, one_mul]

theorem exists_involutions_mul_eq_of_odd_ne_one (h : IsL2Pair X S q) {x : X}
    (hodd : Odd (orderOf x)) (hx1 : x ≠ 1) :
    ∃ a b : X, a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ x = a * b := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h.exists_involutions_mul_eq x
  refine ⟨a, b, ha, hb, fun h1 => hx1 ?_, fun h1 => hx1 ?_, fun h1 => hx1 ?_, rfl⟩
  · rw [h1, one_mul]
    rw [h1, one_mul] at hodd
    exact eq_one_of_mul_self_eq_one_of_odd hb hodd
  · rw [h1, mul_one]
    rw [h1, mul_one] at hodd
    exact eq_one_of_mul_self_eq_one_of_odd ha hodd
  · rw [h1]
    exact hb

end IsL2Pair

end CFSG.CGT.Timmesfeld75
