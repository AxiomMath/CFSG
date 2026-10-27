module

public import CFSG.CGT.Timmesfeld75.StrongClosure

public section

namespace CFSG.CGT.T75P

open CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G] {x y : G}

theorem dih_odd (hx : x * x = 1) (hy : y * y = 1) (hodd : Odd (orderOf (x * y))) :
    ∃ k : ℕ, ((x * y) ^ k)⁻¹ * x * (x * y) ^ k = y := by
  obtain ⟨k, hk⟩ := hodd
  have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
  have hpow : (x * y) ^ (2 * (k + 1)) = x * y := by
    rw [show 2 * (k + 1) = orderOf (x * y) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [hpow] at h1
  exact ⟨k + 1, h1.trans (invol_eq_inv_mul_mul hy).symm⟩

theorem dih_two_mod_four (hx : x * x = 1) (hy : y * y = 1) {m : ℕ} (hm : Odd m)
    (hN : orderOf (x * y) = 2 * m) :
    ∃ z : G, z * z = 1 ∧ x * z = z * x ∧ y * z = z * y ∧
      ∃ k : ℕ, ((x * y) ^ k)⁻¹ * x * (x * y) ^ k = y * z := by
  have hzz : (x * y) ^ m * (x * y) ^ m = 1 := by
    rw [← pow_add, ← two_mul, ← hN]
    exact pow_orderOf_eq_one _
  have hzinv : ((x * y) ^ m)⁻¹ = (x * y) ^ m := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ m = (x * y) ^ m * x := by
    have h1 : x * (x * y) ^ m * x⁻¹ = (x * y) ^ m := by
      rw [← conj_pow, left_invol_inverts hx hy, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hxw : x * (x * y) = y := by rw [← mul_assoc, hx, one_mul]
  have hyz : y * (x * y) ^ m = (x * y) ^ m * y := by
    calc y * (x * y) ^ m = x * (x * y) * (x * y) ^ m := by rw [hxw]
      _ = x * ((x * y) * (x * y) ^ m) := mul_assoc _ _ _
      _ = x * ((x * y) ^ m * (x * y)) := by rw [(Commute.self_pow (x * y) m).eq]
      _ = (x * (x * y) ^ m) * (x * y) := (mul_assoc _ _ _).symm
      _ = ((x * y) ^ m * x) * (x * y) := by rw [hxz]
      _ = (x * y) ^ m * (x * (x * y)) := mul_assoc _ _ _
      _ = (x * y) ^ m * y := by rw [hxw]
  refine ⟨(x * y) ^ m, hzz, hxz, hyz, ?_⟩
  obtain ⟨k, hk⟩ := hm
  refine ⟨k + 1, ?_⟩
  have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hx hy) (k + 1)
  calc ((x * y) ^ (k + 1))⁻¹ * x * (x * y) ^ (k + 1) = ((x * y) ^ (2 * (k + 1)))⁻¹ * x := h1
    _ = ((x * y) ^ m * (x * y))⁻¹ * x := by
        rw [show 2 * (k + 1) = m + 1 by omega, pow_succ]
    _ = (x * y)⁻¹ * (x * y) ^ m * x := by rw [mul_inv_rev ((x * y) ^ m) (x * y), hzinv]
    _ = (x * y)⁻¹ * ((x * y) ^ m * x) := mul_assoc _ _ _
    _ = (x * y)⁻¹ * (x * (x * y) ^ m) := by rw [hxz]
    _ = (x * y)⁻¹ * x * (x * y) ^ m := (mul_assoc _ _ _).symm
    _ = y * (x * y) ^ m := by rw [← invol_eq_inv_mul_mul hy]

theorem pow_succ_inv_aux (r : G) (j : ℕ) : (r ^ (2 * j + 1))⁻¹ = (r ^ (2 * j))⁻¹ * r⁻¹ := by
  rw [pow_succ', mul_inv_rev]

theorem dih_four_dvd (hx : x * x = 1) (hy : y * y = 1) (hpos : 0 < orderOf (x * y))
    (h4 : 4 ∣ orderOf (x * y)) :
    ∃ e z : G, ((∃ g : G, e = g⁻¹ * x * g) ∨ ∃ g : G, e = g⁻¹ * y * g) ∧
      orderOf (e * x) = 4 ∧ (e * x) ^ 2 = z ∧ z * z = 1 ∧ x * z = z * x ∧ y * z = z * y := by
  obtain ⟨q, hq⟩ := h4
  have hq0 : 0 < q := by omega
  have hxr := left_invol_inverts hx hy
  have hyr := right_invol_inverts hx hy
  have hr4 : (x * y) ^ (4 * q) = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  have hzz : (x * y) ^ (2 * q) * (x * y) ^ (2 * q) = 1 := by
    rw [← pow_add, show 2 * q + 2 * q = 4 * q by ring, hr4]
  have hzinv : ((x * y) ^ (2 * q))⁻¹ = (x * y) ^ (2 * q) := inv_eq_of_mul_eq_one_right hzz
  have hxz : x * (x * y) ^ (2 * q) = (x * y) ^ (2 * q) * x := by
    have h1 : x * (x * y) ^ (2 * q) * x⁻¹ = (x * y) ^ (2 * q) := by
      rw [← conj_pow, hxr, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hyz : y * (x * y) ^ (2 * q) = (x * y) ^ (2 * q) * y := by
    have h1 : y * (x * y) ^ (2 * q) * y⁻¹ = (x * y) ^ (2 * q) := by
      rw [← conj_pow, hyr, inv_pow, hzinv]
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hex : ((x * y) ^ q)⁻¹ * x * x = ((x * y) ^ q)⁻¹ := by rw [mul_assoc, hx, mul_one]
  refine ⟨((x * y) ^ q)⁻¹ * x, (x * y) ^ (2 * q), ?_, ?_, ?_, hzz, hxz, hyz⟩
  · rcases Nat.even_or_odd q with ⟨j, hj⟩ | ⟨j, hj⟩
    · left
      refine ⟨(x * y) ^ j, ?_⟩
      rw [inv_pow_mul_mul_pow_of_inverts hxr j, show q = 2 * j by omega]
    · right
      refine ⟨(x * y) ^ j, ?_⟩
      rw [inv_pow_mul_mul_pow_of_inverts hyr j, show q = 2 * j + 1 by omega, pow_succ_inv_aux,
        mul_assoc, ← invol_eq_inv_mul_mul hy]
  · rw [hex, orderOf_inv, orderOf_pow_of_dvd hq0.ne' ⟨4, by rw [hq]; ring⟩, hq]
    exact Nat.mul_div_cancel 4 hq0
  · rw [hex, pow_two, ← mul_inv_rev, ← pow_add, ← two_mul, hzinv]

end CFSG.CGT.T75P
