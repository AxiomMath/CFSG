module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthArith

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f q : ℕ}

theorem te6Core_mul_o4Val_ne_zero3 (hq3p : 3 ≤ q) : te6Core q * o4Val q ≠ 0 := by
  have h1 : 1 ≤ q := by omega
  have h2 : 1 < q ^ 2 := by nlinarith
  unfold te6Core o4Val
  refine mul_ne_zero ?_ ?_
  · refine mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) ?_
    have : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by omega) (by omega)) (by positivity)) ?_
    omega


theorem plus_impossible3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq3p : 3 ≤ q) {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
        (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j)))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
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
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have hj : j = 1 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
    omega
  subst hj
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq3 : 1 ≤ q ^ (1 + 1 + 1) := Nat.one_le_pow _ _ hq1
  have hq4 : 1 ≤ q ^ (1 + 1) := Nat.one_le_pow _ _ hq1
  have hq3' : 1 ≤ q ^ 1 := Nat.one_le_pow _ _ hq1
  unfold te6Core o4Val at h
  zify [hq1, hq2, hq3, hq4, hq3', Nat.one_le_pow 1 q hq1] at h
  have hqz : (0 : ℤ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq2z : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by
    have : (9 : ℤ) ≤ (q : ℤ) ^ 2 := by
      have : (3 : ℤ) ≤ q := by exact_mod_cast hq3p
      nlinarith
    linarith
  have hpos : (0 : ℤ) < (q : ℤ) ^ 7 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) ^ 2 := by positivity
  have h0 : -4 * (q : ℤ) ^ 7 * ((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 2 - 1) ^ 2 = 0 := by
    linear_combination h
  linarith


theorem minus_eq3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f) (hq3p : 3 ≤ q)
    {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * (((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
        (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1))))) : j = 0 := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
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
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega


theorem odd_impossible3 (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hqdef : q = p ^ f)
    (hq3p : 3 ≤ q) {j : ℕ}
    (h : te6Core q * o4Val q =
      2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1)))) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have hL : te6Core q * o4Val q =
      ((q ^ 2 + 1) * (q * (q - 1) + 1) * ((q ^ 2 - 1) * (q + 1) * ((q - 1) * 2))) *
        p ^ (f * 6) := by
    rw [pow_mul, ← hqdef]
    unfold te6Core o4Val
    ring
  have hR : 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
        ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1))) =
      (2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1))) * p ^ (f * (4 * j + 4)) := by
    have e : p ^ (f * (4 * j + 4)) = q ^ (4 * j + 4) := by rw [pow_mul, ← hqdef]
    rw [e]
    ring
  have hU₂ : ¬ p ∣ 2 * ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1)) :=
    not_dvd_mul hp (not_dvd_two hp hp2) (not_dvd_mul hp
      (pow_sub_one_coprime hp hpq hq1 (by omega)) (pow_sub_one_coprime hp hpq hq1 (by omega)))
  have hx := pow_eq_of_mul_eq hp (core_coprime hp hp2 hpq hq1) hU₂ (hL.symm.trans (h.trans hR))
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

end CFSG.ClassicalInvolution.Q3.Q3E6T
