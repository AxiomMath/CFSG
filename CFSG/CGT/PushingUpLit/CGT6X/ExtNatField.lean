module

public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinusField

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight

variable (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem two_eq_zero_Fq : (2 : Fq (2 * n)) = 0 := CharP.cast_eq_zero _ 2

omit [NeZero n] in
theorem exists_mul_self_eq (x : Fq (2 * n)) : ∃ t : Fq (2 * n), t * t = x := by
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (F := Fq (2 * n)) (ringChar.eq _ 2) x
  exact ⟨t, ht.symm⟩

theorem exists_norm_one_ne_one : ∃ a : Fq (2 * n), a ≠ 1 ∧ a * sigR n a = 1 := by
  obtain ⟨w, hw⟩ := exists_sigR_ne n
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero _)
  have hσ : sigR n w ≠ 0 := by
    intro h
    exact hw0 ((sigR n).injective (h.trans (map_zero _).symm))
  refine ⟨sigR n w / w, ?_, ?_⟩
  · intro h
    exact hw (by rwa [div_eq_one_iff_eq hw0] at h)
  · rw [map_div₀, sigR_sigR]
    field_simp

theorem exists_add_sigR_ne : ∃ a : Fq (2 * n), a + sigR n a ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_sigR_ne n
  refine ⟨w, fun h => hw ?_⟩
  have h2 := two_eq_zero_Fq n
  linear_combination h - w * h2

theorem exists_ne_sigR_sq (hn : 2 ≤ n) : ∃ a : Fq (2 * n), a ≠ sigR n a ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := NeZero.ne n
  have : Fintype (Fq (2 * n)) := Fintype.ofFinite _
  have hcard : Fintype.card (Fq (2 * n)) = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n) (by omega)]
  have hall : ∀ a : Fq (2 * n), a ^ 2 ^ (n + 1) = a := by
    intro a
    have := hcon a
    rw [sigR_apply, ← pow_mul, ← pow_succ] at this
    exact this.symm
  set p : Polynomial (Fq (2 * n)) := Polynomial.X ^ 2 ^ (n + 1) - Polynomial.X with hp
  have hm : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
  have hdeg : p.natDegree = 2 ^ (n + 1) := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X, hm]
  have hzero : p = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p Finset.univ ?_ ?_
    · intro a _
      simp [hp, hall a]
    · rw [hdeg, Finset.card_univ, hcard]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [hzero, Polynomial.natDegree_zero] at hdeg
  omega

theorem cube_eq_one_of_one (hn : n = 1) {t : Fq (2 * n)} (ht : t ≠ 0) : t ^ 3 = 1 := by
  have : Fintype (Fq (2 * n)) := Fintype.ofFinite _
  have hc : Fintype.card (Fq (2 * n)) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (2 * n) (by have := NeZero.ne n; omega)]
    have : 2 ^ (2 * n) = 4 := by rw [hn]; norm_num
    exact this
  have := FiniteField.pow_card_sub_one_eq_one t ht
  rwa [hc] at this

omit [NeZero n] in
theorem sigR_eq_mul_self_of_one (hn : n = 1) (x : Fq (2 * n)) : sigR n x = x * x := by
  rw [sigR_apply]
  have : 2 ^ n = 2 := by rw [hn]; norm_num
  rw [this]
  ring

theorem mul_sigR_eq_one_of_one (hn : n = 1) {t : Fq (2 * n)} (ht : t ≠ 0) :
    t * sigR n t = 1 := by
  rw [sigR_eq_mul_self_of_one n hn]
  have := cube_eq_one_of_one n hn ht
  linear_combination this

end CFSG.CGT.PushingUpLit.CGT6X
