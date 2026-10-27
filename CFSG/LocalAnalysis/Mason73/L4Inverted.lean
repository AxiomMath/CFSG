module

public import CFSG.LocalAnalysis.Mason73.Powers2
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv

variable {n : ℕ}

theorem two_pow_nsmul_vec_eq_zero (d : Fin 4 → ZMod (2 ^ n)) : (2 ^ n) • d = 0 := by
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem neg_hh_mul (hn : 1 ≤ n) (a : ZMod (2 ^ n)) : -(hh n * a) = hh n * a := by
  rw [neg_eq_iff_add_eq_zero, ← two_mul, ← mul_assoc, two_mul_hh hn, zero_mul]

theorem hh_mul_add_eq_of_sum (hn : 1 ≤ n) {a b c e : ZMod (2 ^ n)} (h : a + b + c + e = 0) :
    hh n * (a + b) = hh n * (c + e) := by
  have hce : c + e = -(a + b) := by linear_combination h
  rw [hce, mul_neg, neg_hh_mul hn]

theorem hh_mul_two_mul (hn : 1 ≤ n) (a : ZMod (2 ^ n)) : hh n * (a + a) = 0 := by
  rw [← two_mul, ← mul_assoc, mul_comm (hh n) 2, two_mul_hh hn, zero_mul]

theorem hh_mul_eq_zero_of_four_mul (hn : 3 ≤ n) {a : ZMod (2 ^ n)} (ha : 4 * a = 0) :
    hh n * a = 0 := by
  have h4 : hh n = ((2 ^ (n - 3) : ℕ) : ZMod (2 ^ n)) * 4 := by
    rw [hh, show (4 : ZMod (2 ^ n)) = ((4 : ℕ) : ZMod (2 ^ n)) by norm_num, ← Nat.cast_mul,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, show n - 3 + 2 = n - 1 by omega]
  rw [h4, mul_assoc, ha, mul_zero]

theorem el_one_pow_two_pow {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) :
    el d 1 h ^ (2 ^ n) = 1 := by
  rw [el_one_pow h, ← el_zero_one]
  exact el_congr _ _ (two_pow_nsmul_vec_eq_zero d) rfl

theorem el_sq_of_mul_self {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π)
    (hπ : π * π = 1) :
    el d π h ^ 2 = el (d + pv (π : Perm (Fin 4)) d) 1 (hπ ▸ detSum_mul h h) := by
  rw [pow_two, el_mul]
  exact el_congr _ _ rfl hπ

theorem el_pow_two_pow_eq_one_of_isConst (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)}
    {π : Fin81.R0} (h : detSum d π) (hπ : π * π = 1)
    (hc : IsConst fun i => hh n * (d i + pv (π : Perm (Fin 4)) d i)) :
    el d π h ^ (2 ^ n) = 1 := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpow : el d π h ^ (2 ^ n) = (el d π h ^ 2) ^ (2 ^ (n - 1)) := by
    rw [← pow_mul, ← h2]
  rw [hpow, el_sq_of_mul_self h hπ, el_one_pow, el_one_eq_one_iff hn]
  intro i j
  rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  exact hc i j

theorem pow_two_pow_eq_one_of_pow_four {G : Type*} [Monoid G] (hn : 2 ≤ n) {x : G}
    (hx : x ^ 4 = 1) : x ^ (2 ^ n) = 1 := by
  have h4 : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h4, pow_mul, hx, one_pow]

theorem pow_four_eq_sq_sq {G : Type*} [Monoid G] (x : G) : x ^ 4 = (x ^ 2) ^ 2 := by
  rw [← pow_mul]

theorem pow_four_eq_mul_mul {G : Type*} [Monoid G] (x : G) : x ^ 4 = x * x * (x * x) := by
  rw [pow_four_eq_sq_sq, pow_two, pow_two]

theorem R0_comm_s01 : ∀ σ : Fin81.R0, σ * s01 = s01 * σ →
    σ = 1 ∨ σ = s01 ∨ σ = s23 ∨ σ = zP := by
  decide

theorem R0_comm_s23 : ∀ σ : Fin81.R0, σ * s23 = s23 * σ →
    σ = 1 ∨ σ = s01 ∨ σ = s23 ∨ σ = zP := by
  decide

theorem isConst_add_pv_of_conj_eq_inv (hn : 2 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)}
    {π σ : Fin81.R0} (hd : detSum d π) (he : detSum e σ) (hπ : π * π = 1)
    (h : el e σ he * el d π hd * (el e σ he)⁻¹ = (el d π hd)⁻¹) :
    IsConst ((d + pv (π : Perm (Fin 4)) d) +
      pv (σ : Perm (Fin 4)) (d + pv (π : Perm (Fin 4)) d)) := by
  have hsq : el e σ he * el d π hd ^ 2 * (el e σ he)⁻¹ = (el d π hd ^ 2)⁻¹ := by
    rw [← conj_pow, h, inv_pow]
  rw [el_sq_of_mul_self hd hπ, el_conj hn he, el_one_inv, el_eq_el_iff hn] at hsq
  have hc := hsq.2
  rw [← isConst_neg_iff]
  intro i j
  have := hc i j
  simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply] at this ⊢
  linear_combination this

theorem el_s01_pow_two_pow_of_conj_eq_inv (hn : 3 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)}
    {σ : Fin81.R0} (hd : detSum d s01) (he : detSum e σ)
    (h : el e σ he * el d s01 hd * (el e σ he)⁻¹ = (el d s01 hd)⁻¹) :
    el d s01 hd ^ (2 ^ n) = 1 := by
  have hπ : s01 * s01 = (1 : Fin81.R0) := by decide
  have hσ : σ * s01 = s01 * σ := by
    have h1 := congrArg piT h
    rw [map_mul, map_mul, map_inv, map_inv, piT_el, piT_el] at h1
    have h2 : s01⁻¹ = s01 := by decide
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hc := isConst_add_pv_of_conj_eq_inv (by omega) hd he hπ h
  rw [pv_s01] at hc
  have hsum : d 0 + d 1 + d 2 + d 3 + hh n = 0 := by
    have := hd
    rw [detSum, sgnH_s01 (by omega), Fin.sum_univ_four] at this
    exact this
  rcases R0_comm_s01 σ hσ with rfl | rfl | rfl | rfl
  ·
    refine pow_two_pow_eq_one_of_pow_four (by omega) ?_
    rw [pow_four_eq_sq_sq, el_sq_of_mul_self hd hπ, el_one_pow,
      el_one_eq_one_iff (by omega), pv_s01]
    intro i j
    have := hc i j
    simp only [OneMemClass.coe_one, pv_one, Pi.add_apply] at this
    simp only [Pi.smul_apply, Pi.add_apply, two_nsmul]
    exact this
  ·
    refine pow_two_pow_eq_one_of_pow_four (by omega) ?_
    rw [pow_four_eq_sq_sq, el_sq_of_mul_self hd hπ, el_one_pow,
      el_one_eq_one_iff (by omega), pv_s01]
    rw [pv_s01] at hc
    refine isConst_of_eq_four (d 0 + d 1 + (d 0 + d 1)) ?_ ?_ ?_ ?_
    · show 2 • (d 0 + d 1) = d 0 + d 1 + (d 0 + d 1)
      rw [two_nsmul]
    · show 2 • (d 1 + d 0) = d 0 + d 1 + (d 0 + d 1)
      rw [two_nsmul, add_comm (d 1)]
    · have := hc 2 0
      simp only [Pi.add_apply, Matrix.cons_val] at this
      show 2 • (d 2 + d 2) = d 0 + d 1 + (d 0 + d 1)
      rw [two_nsmul]
      linear_combination this
    · have := hc 3 0
      simp only [Pi.add_apply, Matrix.cons_val] at this
      show 2 • (d 3 + d 3) = d 0 + d 1 + (d 0 + d 1)
      rw [two_nsmul]
      linear_combination this
  ·
    rw [pv_s23] at hc
    have h02 := hc 0 2
    simp only [Pi.add_apply, Matrix.cons_val] at h02
    have h4 : 4 * (d 0 + d 1) = 0 := by
      linear_combination h02 + 2 * hsum - (two_mul_hh (n := n) (by omega))
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd hπ (isConst_of_eq_four 0 ?_ ?_ ?_ ?_) <;>
      simp only [pv_s01, Matrix.cons_val]
    · exact hh_mul_eq_zero_of_four_mul hn h4
    · rw [add_comm (d 1)]
      exact hh_mul_eq_zero_of_four_mul hn h4
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_two_mul (by omega) _
  ·
    rw [pv_zP] at hc
    have h02 := hc 0 2
    simp only [Pi.add_apply, Matrix.cons_val] at h02
    have h4 : 4 * (d 0 + d 1) = 0 := by
      linear_combination h02 + 2 * hsum - (two_mul_hh (n := n) (by omega))
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd hπ (isConst_of_eq_four 0 ?_ ?_ ?_ ?_) <;>
      simp only [pv_s01, Matrix.cons_val]
    · exact hh_mul_eq_zero_of_four_mul hn h4
    · rw [add_comm (d 1)]
      exact hh_mul_eq_zero_of_four_mul hn h4
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_two_mul (by omega) _

theorem el_s23_pow_two_pow_of_conj_eq_inv (hn : 3 ≤ n) {d e : Fin 4 → ZMod (2 ^ n)}
    {σ : Fin81.R0} (hd : detSum d s23) (he : detSum e σ)
    (h : el e σ he * el d s23 hd * (el e σ he)⁻¹ = (el d s23 hd)⁻¹) :
    el d s23 hd ^ (2 ^ n) = 1 := by
  have hπ : s23 * s23 = (1 : Fin81.R0) := by decide
  have hσ : σ * s23 = s23 * σ := by
    have h1 := congrArg piT h
    rw [map_mul, map_mul, map_inv, map_inv, piT_el, piT_el] at h1
    have h2 : s23⁻¹ = s23 := by decide
    rw [h2] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hc := isConst_add_pv_of_conj_eq_inv (by omega) hd he hπ h
  rw [pv_s23] at hc
  have hsum : d 0 + d 1 + d 2 + d 3 + hh n = 0 := (detSum_s23_iff (by omega)).1 hd
  rcases R0_comm_s23 σ hσ with rfl | rfl | rfl | rfl
  ·
    refine pow_two_pow_eq_one_of_pow_four (by omega) ?_
    rw [pow_four_eq_sq_sq, el_sq_of_mul_self hd hπ, el_one_pow,
      el_one_eq_one_iff (by omega), pv_s23]
    intro i j
    have := hc i j
    simp only [OneMemClass.coe_one, pv_one, Pi.add_apply] at this
    simp only [Pi.smul_apply, Pi.add_apply, two_nsmul]
    exact this
  ·
    rw [pv_s01] at hc
    have h02 := hc 0 2
    simp only [Pi.add_apply, Matrix.cons_val] at h02
    have h4 : 4 * (d 2 + d 3) = 0 := by
      linear_combination -h02 + 2 * hsum - (two_mul_hh (n := n) (by omega))
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd hπ (isConst_of_eq_four 0 ?_ ?_ ?_ ?_) <;>
      simp only [pv_s23, Matrix.cons_val]
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_eq_zero_of_four_mul hn h4
    · rw [add_comm (d 3)]
      exact hh_mul_eq_zero_of_four_mul hn h4
  ·
    refine pow_two_pow_eq_one_of_pow_four (by omega) ?_
    rw [pow_four_eq_sq_sq, el_sq_of_mul_self hd hπ, el_one_pow,
      el_one_eq_one_iff (by omega), pv_s23]
    rw [pv_s23] at hc
    refine isConst_of_eq_four (d 2 + d 3 + (d 2 + d 3)) ?_ ?_ ?_ ?_
    · have := hc 0 2
      simp only [Pi.add_apply, Matrix.cons_val] at this
      show 2 • (d 0 + d 0) = d 2 + d 3 + (d 2 + d 3)
      rw [two_nsmul]
      linear_combination this
    · have := hc 1 2
      simp only [Pi.add_apply, Matrix.cons_val] at this
      show 2 • (d 1 + d 1) = d 2 + d 3 + (d 2 + d 3)
      rw [two_nsmul]
      linear_combination this
    · show 2 • (d 2 + d 3) = d 2 + d 3 + (d 2 + d 3)
      rw [two_nsmul]
    · show 2 • (d 3 + d 2) = d 2 + d 3 + (d 2 + d 3)
      rw [two_nsmul, add_comm (d 3)]
  ·
    rw [pv_zP] at hc
    have h02 := hc 0 2
    simp only [Pi.add_apply, Matrix.cons_val] at h02
    have h4 : 4 * (d 2 + d 3) = 0 := by
      linear_combination -h02 + 2 * hsum - (two_mul_hh (n := n) (by omega))
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd hπ (isConst_of_eq_four 0 ?_ ?_ ?_ ?_) <;>
      simp only [pv_s23, Matrix.cons_val]
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_two_mul (by omega) _
    · exact hh_mul_eq_zero_of_four_mul hn h4
    · rw [add_comm (d 3)]
      exact hh_mul_eq_zero_of_four_mul hn h4

theorem pow_two_pow_eq_one_of_conj_eq_inv (hn : 3 ≤ n) {x y : L4Model n}
    (h : y * x * y⁻¹ = x⁻¹) : x ^ (2 ^ n) = 1 := by
  obtain ⟨d, π, hd, rfl⟩ := exists_eq_el x
  obtain ⟨e, σ, he, rfl⟩ := exists_eq_el y
  have hsum0 : Perm.sign (π : Perm (Fin 4)) = 1 → d 0 + d 1 + d 2 + d 3 = 0 :=
    fun hs => (detSum_even_iff hs).1 hd
  rcases R0_cases (π : Perm (Fin 4)) π.2 with hπ | hπ | hπ | hπ | hπ | hπ | hπ
  · obtain rfl : π = 1 := Subtype.ext hπ
    exact el_one_pow_two_pow hd
  · obtain rfl : π = s01 := Subtype.ext hπ
    exact el_s01_pow_two_pow_of_conj_eq_inv hn hd he h
  · obtain rfl : π = s23 := Subtype.ext hπ
    exact el_s23_pow_two_pow_of_conj_eq_inv hn hd he h
  · obtain rfl : π = zP := Subtype.ext hπ
    have hs := hsum0 (by decide)
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd (by decide) ?_
    rw [pv_zP]
    refine isConst_of_eq_four (hh n * (d 0 + d 1)) rfl ?_ ?_ ?_
    · show hh n * (d 1 + d 0) = hh n * (d 0 + d 1)
      rw [add_comm (d 1)]
    · show hh n * (d 2 + d 3) = hh n * (d 0 + d 1)
      exact (hh_mul_add_eq_of_sum (by omega) hs).symm
    · show hh n * (d 3 + d 2) = hh n * (d 0 + d 1)
      rw [add_comm (d 3)]
      exact (hh_mul_add_eq_of_sum (by omega) hs).symm
  · obtain rfl : π = tP := Subtype.ext hπ
    have hs := hsum0 (by decide)
    have hs' : d 0 + d 2 + d 1 + d 3 = 0 := by linear_combination hs
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd (by decide) ?_
    rw [pv_tP]
    refine isConst_of_eq_four (hh n * (d 0 + d 2)) rfl ?_ ?_ ?_
    · show hh n * (d 1 + d 3) = hh n * (d 0 + d 2)
      exact (hh_mul_add_eq_of_sum (by omega) hs').symm
    · show hh n * (d 2 + d 0) = hh n * (d 0 + d 2)
      rw [add_comm (d 2)]
    · show hh n * (d 3 + d 1) = hh n * (d 0 + d 2)
      rw [add_comm (d 3)]
      exact (hh_mul_add_eq_of_sum (by omega) hs').symm
  · obtain rfl : π = tzP := Subtype.ext hπ
    have hs := hsum0 (by decide)
    have hs' : d 0 + d 3 + d 1 + d 2 = 0 := by linear_combination hs
    refine el_pow_two_pow_eq_one_of_isConst (by omega) hd (by decide) ?_
    rw [pv_tzP]
    refine isConst_of_eq_four (hh n * (d 0 + d 3)) rfl ?_ ?_ ?_
    · show hh n * (d 1 + d 2) = hh n * (d 0 + d 3)
      exact (hh_mul_add_eq_of_sum (by omega) hs').symm
    · show hh n * (d 2 + d 1) = hh n * (d 0 + d 3)
      rw [add_comm (d 2)]
      exact (hh_mul_add_eq_of_sum (by omega) hs').symm
    · show hh n * (d 3 + d 0) = hh n * (d 0 + d 3)
      rw [add_comm (d 3)]
  · refine pow_two_pow_eq_one_of_pow_four (by omega) ?_
    have hb : piT (el d π hd) * piT (el d π hd) = zP := by
      rw [piT_el]
      exact Subtype.ext hπ
    have h4 := mul_self_mul_self_eq_one_of_piT_zP (by omega) hb
    rw [pow_four_eq_mul_mul]
    exact h4

end CFSG.LocalAnalysis.Mason73
