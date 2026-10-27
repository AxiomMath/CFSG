module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Factorization.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem sec4F_two_part [Finite G] (g : G) :
    ∃ x o : G, x ∈ Subgroup.zpowers g ∧ o ∈ Subgroup.zpowers g ∧ g = x * o ∧
      (∃ n : ℕ, x ^ (2 ^ n) = 1) ∧ Odd (orderOf o) := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, ((2 ^ k : ℕ) : ℤ) * u + (m : ℤ) * v = 1 := by
    refine ⟨Nat.gcdA (2 ^ k) m, Nat.gcdB (2 ^ k) m, ?_⟩
    have h := Nat.gcd_eq_gcd_ab (2 ^ k) m
    rw [hcop.gcd_eq_one] at h
    simpa using h.symm
  have hord : ((2 ^ k : ℕ) : ℤ) * (m : ℤ) = (orderOf g : ℤ) := by
    rw [hkm, Nat.cast_mul, Nat.cast_pow]
  refine ⟨g ^ ((m : ℤ) * v), g ^ (((2 ^ k : ℕ) : ℤ) * u), ?_, ?_, ?_, ⟨k, ?_⟩, ?_⟩
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  · rw [← zpow_add, add_comm, huv, zpow_one]
  · have h : (m : ℤ) * v * ((2 ^ k : ℕ) : ℤ) = (orderOf g : ℤ) * v := by
      rw [mul_assoc, mul_comm v, ← mul_assoc, mul_comm (m : ℤ) ((2 ^ k : ℕ) : ℤ), hord]
    rw [← zpow_natCast, ← zpow_mul, h, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  · have h : ((2 ^ k : ℕ) : ℤ) * u * (m : ℤ) = (orderOf g : ℤ) * u := by
      rw [mul_assoc, mul_comm u, ← mul_assoc, hord]
    have h1 : (g ^ (((2 ^ k : ℕ) : ℤ) * u)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, h, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)

end CFSG.OddStandard.SmallF3.Omega
