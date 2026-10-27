module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.SG_two_signalizer_completeness

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

open scoped commutatorElement

section Crit

variable {W : Type} [Group W]

theorem exists_odd_decomp [Finite W] {f n : W} (hc : Commute f n) (hx : Odd (orderOf (f * n))) :
    ∃ r : ℕ, Odd (orderOf (f ^ r)) ∧ Odd (orderOf (n ^ r)) ∧ f * n = f ^ r * n ^ r := by
  set e := orderOf f * orderOf n with he
  have hepos : e ≠ 0 := (Nat.mul_pos (orderOf_pos f) (orderOf_pos n)).ne'
  obtain ⟨S, e', he', hee⟩ := Nat.exists_eq_two_pow_mul_odd hepos
  have hcop : Nat.Coprime (2 ^ S) (orderOf (f * n)) :=
    Nat.Coprime.pow_left S (Nat.coprime_two_left.mpr hx)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hfe : f ^ e = 1 := by
    rw [he, pow_mul, pow_orderOf_eq_one, one_pow]
  have hne : n ^ e = 1 := by
    rw [he, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hr : 2 ^ S * m * e' = e * m := by rw [hee]; ring
  refine ⟨2 ^ S * m, ?_, ?_, ?_⟩
  · have h1 : (f ^ (2 ^ S * m)) ^ e' = 1 := by
      rw [← pow_mul, hr, pow_mul, hfe, one_pow]
    exact he'.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · have h1 : (n ^ (2 ^ S * m)) ^ e' = 1 := by
      rw [← pow_mul, hr, pow_mul, hne, one_pow]
    exact he'.of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)
  · rw [← hc.mul_pow, pow_mul, hm]

end Crit

end CFSG.OddStandard.Solomon75
