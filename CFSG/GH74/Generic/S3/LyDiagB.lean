module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.Generic.S3

open Subgroup

section

variable {Y : Type} [Group Y]

theorem eq_one_of_sq_eq_one_of_odd {N : Subgroup Y} (hN : Odd (Nat.card N)) {a : Y} (ha : a ∈ N)
    (h : a ^ 2 = 1) : a = 1 := by
  have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf a ∣ Nat.card N := by
    have := Subgroup.orderOf_dvd_natCard N ha
    simpa using this
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · exfalso
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h2)

theorem exists_order_four_inverted {N : Subgroup Y} [N.Normal] (hN : Odd (Nat.card N)) {y x z : Y}
    (hy2 : y * y = 1) (hyc : ∀ g : Y, g * y = y * g) (hx : x * x = 1) (hz : z * z = 1)
    (hbar : (x * z) ^ 2 * y⁻¹ ∈ N) : ∃ t : Y, t ^ 2 = y ∧ x * t * x = t⁻¹ := by
  set r : Y := x * z with hr
  set u : Y := r ^ 2 * y⁻¹ with hu
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have huN : u ∈ N := hbar
  have hr2 : r ^ 2 = u * y := by rw [hu, hy', mul_assoc, hy2, mul_one]
  have hcomm : Commute u y := hyc u
  have hr4 : r ^ 4 = u ^ 2 := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (u * y) ^ 2 := by rw [hr2]
      _ = u ^ 2 * y ^ 2 := hcomm.mul_pow 2
      _ = u ^ 2 := by rw [pow_two y, hy2, mul_one]
  have hr4N : r ^ 4 ∈ N := by rw [hr4]; exact N.pow_mem huN 2
  have hxrx : x * r * x = r⁻¹ := by
    have h1 : r⁻¹ = z * x := by
      rw [hr, mul_inv_rev, hx', hz']
    rw [h1]
    calc x * r * x = (x * x) * z * x := by rw [hr]; group
      _ = z * x := by rw [hx, one_mul]
  set k := orderOf (r ^ 4) with hk
  have hkodd : Odd k := by
    have hd : orderOf (r ^ 4) ∣ Nat.card N := by
      have := Subgroup.orderOf_dvd_natCard N hr4N
      simpa using this
    exact hN.of_dvd_nat hd
  refine ⟨r ^ k, ?_, ?_⟩
  · have hukN : u ^ k ∈ N := N.pow_mem huN k
    have hu2k : (u ^ k) ^ 2 = 1 := by
      calc (u ^ k) ^ 2 = (u ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ = (r ^ 4) ^ k := by rw [hr4]
        _ = 1 := by rw [hk]; exact pow_orderOf_eq_one _
    have huk1 : u ^ k = 1 := eq_one_of_sq_eq_one_of_odd hN hukN hu2k
    obtain ⟨m, hm⟩ := hkodd
    have hyk : y ^ k = y := by
      rw [hm, pow_succ, pow_mul, pow_two y, hy2, one_pow, one_mul]
    calc (r ^ k) ^ 2 = (r ^ 2) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (u * y) ^ k := by rw [hr2]
      _ = u ^ k * y ^ k := hcomm.mul_pow k
      _ = y := by rw [huk1, hyk, one_mul]
  · calc x * r ^ k * x = x * r ^ k * x⁻¹ := by rw [hx']
      _ = (x * r * x⁻¹) ^ k := (conj_pow).symm
      _ = (r⁻¹) ^ k := by rw [hx', hxrx]
      _ = (r ^ k)⁻¹ := inv_pow r k

theorem exists_conj_of_dihedral {N : Subgroup Y} [N.Normal] (hN : Odd (Nat.card N)) {y x z : Y}
    (hy2 : y * y = 1) (hyc : ∀ g : Y, g * y = y * g) (hx : x * x = 1) (hz : z * z = 1)
    (hbar : (x * z) ^ 2 * y⁻¹ ∈ N) : ∃ g : Y, g⁻¹ * x * g = y * x := by
  obtain ⟨t, ht2, hxt⟩ := exists_order_four_inverted hN hy2 hyc hx hz hbar
  refine ⟨t, ?_⟩
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  calc t⁻¹ * x * t = t⁻¹ * (x * t * x) * x := by
        have hx' : x * x = 1 := hx
        calc t⁻¹ * x * t = t⁻¹ * (x * t * (x * x)) := by rw [hx', mul_one]; group
          _ = t⁻¹ * (x * t * x) * x := by group
    _ = t⁻¹ * t⁻¹ * x := by rw [hxt]
    _ = (t ^ 2)⁻¹ * x := by rw [pow_two, mul_inv_rev]
    _ = y * x := by rw [ht2, hy']

end

end CFSG.GH74.Generic.S3
