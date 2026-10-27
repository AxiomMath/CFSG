module

public import CFSG.ClassicalInvolution.RouteD.TypeF4TwinPerpArith

public section

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f q : ℕ}

theorem f4Core_mul_o4Val_ne_zero3 (hq3 : 3 ≤ q) : f4Core q * o4Val q ≠ 0 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 < q ^ 2 := by nlinarith
  unfold f4Core o4Val
  refine mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) ?_
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by positivity)) ?_
  omega

theorem f4_plus_impossible3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq3 : 3 ≤ q) {j : ℕ}
    (h : f4Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
        (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j)))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hR : 2 * (((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
        (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j))) =
      (2 * ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) * ((q ^ (j + 1) - 1) * (q ^ j + 1)))) *
        p ^ (f * (4 * j + 2)) := by
    have e : p ^ (f * (4 * j + 2)) = q ^ (4 * j + 2) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) *
      ((q ^ (j + 1) - 1) * (q ^ j + 1))) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
        (pow_add_one_coprime hp hp2 hpq _))
      (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
        (pow_add_one_coprime hp hp2 hpq _)))
  have hx := pow_eq_of_mul_eq hp (f4_core_coprime hp hp2 hpq hq1) hU₂
    ((f4Core_mul_o4Val_eq hqdef).symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem f4_minus_impossible3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq3 : 3 ≤ q) {j : ℕ}
    (h : f4Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
        (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1))))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hR : 2 * (((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
        (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1)))) =
      (2 * ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
        ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)))) * p ^ (f * (4 * j + 6)) := by
    have e : p ^ (f * (4 * j + 6)) = q ^ (4 * j + 6) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1))) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
        (pow_sub_one_coprime hp hpq hq1 (by omega)))
      (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
        (pow_sub_one_coprime hp hpq hq1 (by omega))))
  have hx := pow_eq_of_mul_eq hp (f4_core_coprime hp hp2 hpq hq1) hU₂
    ((f4Core_mul_o4Val_eq hqdef).symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem f4_odd_eq3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq3 : 3 ≤ q) {j : ℕ}
    (h : f4Core q * o4Val q =
      2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1)))) : j = 0 := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hR : 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1))) =
      (2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1))) * p ^ (f * (4 * j + 4)) := by
    have e : p ^ (f * (4 * j + 4)) = q ^ (4 * j + 4) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1)) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (pow_sub_one_coprime hp hpq hq1 (by omega)) (pow_sub_one_coprime hp hpq hq1 (by omega)))
  have hx := pow_eq_of_mul_eq hp (f4_core_coprime hp hp2 hpq hq1) hU₂
    ((f4Core_mul_o4Val_eq hqdef).symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
