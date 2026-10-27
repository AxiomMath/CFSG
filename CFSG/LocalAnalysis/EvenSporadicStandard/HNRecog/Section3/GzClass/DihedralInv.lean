module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma dihedralInv_conj_pow {G : Type*} [Group G] {x r : G}
    (h : x * r * x⁻¹ = r⁻¹) (j : ℕ) : x * r ^ j * x⁻¹ = (r⁻¹) ^ j := by
  have hxr : (MulAut.conj x) r = r⁻¹ := by rw [MulAut.conj_apply]; exact h
  have h' := map_pow (MulAut.conj x) r j
  rw [hxr] at h'
  rwa [MulAut.conj_apply] at h'

private lemma dihedralInv_conj_inv {G : Type*} [Group G] {x r : G}
    (h : x * r * x⁻¹ = r⁻¹) : x * r⁻¹ * x⁻¹ = r := by
  have h' := congrArg Inv.inv h
  rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv] at h'
  simpa only [mul_assoc] using h'

private lemma dihedralInv_conj_pow_mul {G : Type*} [Group G] {x r : G}
    (h : x * r * x⁻¹ = r⁻¹) (j : ℕ) : r ^ j * x * (r ^ j)⁻¹ = r ^ (2 * j) * x := by
  have hconj' := dihedralInv_conj_inv h
  have hpow' : x * (r⁻¹) ^ j * x⁻¹ = r ^ j := by
    have := dihedralInv_conj_pow (x := x) (r := r⁻¹) (by simpa using hconj') j
    simpa using this
  have hinv : x * (r ^ j)⁻¹ * x⁻¹ = r ^ j := by
    rwa [inv_pow] at hpow'
  have hxm : x * (r ^ j)⁻¹ = r ^ j * x := by
    have h2 := congrArg (· * x) hinv
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
  calc r ^ j * x * (r ^ j)⁻¹ = r ^ j * (x * (r ^ j)⁻¹) := by rw [mul_assoc]
    _ = r ^ j * (r ^ j * x) := by rw [hxm]
    _ = r ^ j * r ^ j * x := by rw [mul_assoc]
    _ = r ^ (2 * j) * x := by rw [← pow_add, two_mul]

private lemma dihedralInv_conj_pow_self {G : Type*} [Group G] (r : G) (j : ℕ) :
    r ^ j * r * (r ^ j)⁻¹ = r := by
  have hcomm : Commute (r ^ j) r := (Commute.refl r).pow_left j
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma dihedralInv_conj_pow_mul_y {G : Type*} [Group G] {x r y : G} (hy : y = x * r)
    (h : x * r * x⁻¹ = r⁻¹) (j : ℕ) : r ^ j * y * (r ^ j)⁻¹ = r ^ (2 * j) * y := by
  have h1 : MulAut.conj (r ^ j) y = r ^ (2 * j) * y := by
    rw [hy, map_mul, MulAut.conj_apply, MulAut.conj_apply, dihedralInv_conj_pow_mul h j,
      dihedralInv_conj_pow_self r j]
    rw [mul_assoc]
  rwa [MulAut.conj_apply] at h1

theorem isConj_of_odd_orderOf_mul {G : Type*} [Group G] [Finite G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hodd : Odd (orderOf (x * y))) : IsConj x y := by
  set r := x * y with hr
  obtain ⟨k, hk⟩ := hodd
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hyy : y * y = 1 := by simpa [pow_two] using hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hconj : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hy', hx']
    calc x * (x * y) * x = (x * x) * y * x := by rw [← mul_assoc]
      _ = y * x := by rw [hxx, one_mul]
  have hy_eq : y = r⁻¹ * x := by
    rw [hr, mul_inv_rev, hy', hx']
    rw [mul_assoc, hxx, mul_one]
  have hpow_order : r ^ (2 * k) = r⁻¹ := by
    have h1 : r ^ (2 * k) * r = 1 := by
      have h2 := pow_orderOf_eq_one r
      rw [hk, pow_succ] at h2
      exact h2
    exact eq_inv_of_mul_eq_one_left h1
  refine isConj_iff.mpr ⟨r ^ k, ?_⟩
  rw [dihedralInv_conj_pow_mul hconj k, hpow_order]
  exact hy_eq.symm

theorem exists_central_involution_of_even_orderOf_mul {G : Type*} [Group G] [Finite G] {x y : G}
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (heven : Even (orderOf (x * y))) :
    ∃ z₀ : G, (∃ k : ℕ, z₀ = (x * y) ^ k) ∧ z₀ ^ 2 = 1 ∧ z₀ ≠ 1 ∧ z₀ * x = x * z₀ ∧
      z₀ * y = y * z₀ ∧ (IsConj y (z₀ * y) ∨ IsConj y (z₀ * x)) := by
  set r := x * y with hr
  obtain ⟨k, hk⟩ := heven
  have hxx : x * x = 1 := by simpa [pow_two] using hx
  have hyy : y * y = 1 := by simpa [pow_two] using hy
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hconj : x * r * x⁻¹ = r⁻¹ := by
    rw [hr, mul_inv_rev, hy', hx']
    calc x * (x * y) * x = (x * x) * y * x := by rw [← mul_assoc]
      _ = y * x := by rw [hxx, one_mul]
  have hyxr : y = x * r := by
    rw [hr, ← mul_assoc, hxx, one_mul]
  have hy_eq : y = r⁻¹ * x := by
    rw [hr, mul_inv_rev, hy', hx']
    rw [mul_assoc, hxx, mul_one]
  have hpos : 0 < orderOf r := orderOf_pos r
  have hkpos : 0 < k := by omega
  have hklt : k < orderOf r := by omega
  have hk2 : k * 2 = orderOf r := by omega
  have hzk2 : (r ^ k) ^ 2 = 1 := by
    rw [← pow_mul, hk2, pow_orderOf_eq_one]
  have hzk1 : r ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) hklt
  have hzk : r ^ k * r ^ k = 1 := by
    rw [← pow_add, ← hk, pow_orderOf_eq_one]
  have hzinv : (r⁻¹) ^ k = r ^ k := by
    rw [inv_pow]
    exact inv_eq_of_mul_eq_one_right hzk
  have hzx' : r ^ k * x = x * r ^ k := by
    have h := dihedralInv_conj_pow hconj k
    rw [hzinv] at h
    calc r ^ k * x = (x * r ^ k * x⁻¹) * x := by rw [h]
      _ = x * r ^ k * (x⁻¹ * x) := by rw [mul_assoc]
      _ = x * r ^ k := by rw [inv_mul_cancel, mul_one]
  have hzy' : r ^ k * y = y * r ^ k := by
    have hcomm : Commute (r ^ k) r := (Commute.refl r).pow_left k
    rw [hyxr]
    calc r ^ k * (x * r) = r ^ k * x * r := (mul_assoc _ _ _).symm
      _ = x * r ^ k * r := by rw [hzx']
      _ = x * (r ^ k * r) := mul_assoc _ _ _
      _ = x * (r * r ^ k) := by rw [hcomm.eq]
      _ = x * r * r ^ k := (mul_assoc _ _ _).symm
  refine ⟨r ^ k, ⟨k, by rw [hr]⟩, hzk2, hzk1, hzx', hzy', ?_⟩
  by_cases hkeven : Even k
  · left
    obtain ⟨j, hj⟩ := hkeven
    refine isConj_iff.mpr ⟨r ^ j, ?_⟩
    have h2j : 2 * j = k := by omega
    rw [dihedralInv_conj_pow_mul_y hyxr hconj j, h2j]
  · right
    have hkodd : Odd k := Nat.not_even_iff_odd.mp hkeven
    obtain ⟨j, hj⟩ := hkodd
    refine isConj_iff.mpr ⟨r ^ (j + 1), ?_⟩
    have h2j : 2 * (j + 1) = k + 1 := by omega
    have hry : r * y = x := by
      rw [hy_eq, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [dihedralInv_conj_pow_mul_y hyxr hconj (j + 1), h2j, pow_succ, mul_assoc, hry]

end CFSG.EvenSporadicStandard.HNRecog.Section3
