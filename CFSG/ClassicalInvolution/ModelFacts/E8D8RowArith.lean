module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthArith

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalInvolution.RouteD.NonClassical

@[expose] def framePlus (q j : ℕ) : ℕ :=
  ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1)) * q ^ (2 * (j + 1)) *
    (((q ^ (j + 1) - 1) * (q ^ j + 1)) * q ^ (2 * j))

@[expose] def frameMinus (q j : ℕ) : ℕ :=
  ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1)) * q ^ (2 * (j + 1 + 1)) *
    (((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) * q ^ (2 * (j + 1)))

@[expose] def frameOdd (q j : ℕ) : ℕ :=
  (q ^ (2 * (j + 1 + 1)) - 1) * q ^ (2 * (j + 1) + 1) *
    ((q ^ (2 * (j + 1)) - 1) * q ^ (2 * j + 1))

section Valuation

variable {p f q : ℕ}

theorem framePlus_eq (hqdef : q = p ^ f) (j : ℕ) :
    framePlus q j = ((q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) *
      ((q ^ (j + 1) - 1) * (q ^ j + 1))) * p ^ (f * (4 * j + 2)) := by
  have e : p ^ (f * (4 * j + 2)) = q ^ (4 * j + 2) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold framePlus
  ring

theorem frameMinus_eq (hqdef : q = p ^ f) (j : ℕ) :
    frameMinus q j = ((q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1))) * p ^ (f * (4 * j + 6)) := by
  have e : p ^ (f * (4 * j + 6)) = q ^ (4 * j + 6) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold frameMinus
  ring

theorem frameOdd_eq (hqdef : q = p ^ f) (j : ℕ) :
    frameOdd q j = ((q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1)) *
      p ^ (f * (4 * j + 4)) := by
  have e : p ^ (f * (4 * j + 4)) = q ^ (4 * j + 4) := by rw [pow_mul, ← hqdef]
  rw [e]
  unfold frameOdd
  ring

theorem framePlus_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (j + 1 + 1) - 1) * (q ^ (j + 1) + 1) * ((q ^ (j + 1) - 1) * (q ^ j + 1)) :=
  not_dvd_mul hp
    (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
      (pow_add_one_coprime hp hp2 hpq _))
    (not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
      (pow_add_one_coprime hp hp2 hpq _))

theorem frameMinus_coprime (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (j + 1 + 1 + 1) + 1) * (q ^ (j + 1 + 1) - 1) *
      ((q ^ (j + 1 + 1) + 1) * (q ^ (j + 1) - 1)) :=
  not_dvd_mul hp
    (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
      (pow_sub_one_coprime hp hpq hq1 (by omega)))
    (not_dvd_mul hp (pow_add_one_coprime hp hp2 hpq _)
      (pow_sub_one_coprime hp hpq hq1 (by omega)))

theorem frameOdd_coprime (hp : p.Prime) (hpq : p ∣ q) (hq1 : 1 ≤ q) (j : ℕ) :
    ¬ p ∣ (q ^ (2 * (j + 1 + 1)) - 1) * (q ^ (2 * (j + 1)) - 1) :=
  not_dvd_mul hp (pow_sub_one_coprime hp hpq hq1 (by omega))
    (pow_sub_one_coprime hp hpq hq1 (by omega))

end Valuation

section Compare

variable {p f q : ℕ}

theorem framePlus_eq_framePlus_four (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq5 : 5 ≤ q) {j : ℕ} (h : framePlus q j = framePlus q 4) : j = 4 := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [framePlus_eq hqdef, framePlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (framePlus_coprime hp hp2 hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem framePlus_pos (hq2 : 2 ≤ q) (j : ℕ) : 0 < framePlus q j := by
  have h1 : 1 < q ^ (j + 1 + 1) := Nat.one_lt_pow (by omega) (by omega)
  have h2 : 1 < q ^ (j + 1) := Nat.one_lt_pow (by omega) (by omega)
  have h3 : 0 < q := by omega
  unfold framePlus
  refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by positivity))
    (Nat.mul_pos (Nat.mul_pos (by omega) (by positivity)) (by positivity))

theorem frameOdd_ne_framePlus_four (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq5 : 5 ≤ q) {j : ℕ} (h : frameOdd q j = framePlus q 4) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  rw [frameOdd_eq hqdef, framePlus_eq hqdef] at h
  have hx := pow_eq_of_mul_eq hp (frameOdd_coprime hp hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
  omega

theorem frameMinus_ne_framePlus_four (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hqdef : q = p ^ f) (hq5 : 5 ≤ q) {j : ℕ} (h : frameMinus q j = framePlus q 4) : False := by
  have hpq : p ∣ q := dvd_of_eq_pow hf hqdef
  have hq1 : 1 ≤ q := by omega
  have h' := h
  rw [frameMinus_eq hqdef, framePlus_eq hqdef] at h'
  have hx := pow_eq_of_mul_eq hp (frameMinus_coprime hp hp2 hpq hq1 j)
    (framePlus_coprime hp hp2 hpq hq1 4) h'
  have hj : j = 3 := by
    have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f) hx
    omega
  subst hj
  have e1 : frameMinus q 3 =
      (q ^ 6 + 1) * (q ^ 5 - 1) * q ^ 10 * ((q ^ 5 + 1) * (q ^ 4 - 1) * q ^ 8) := rfl
  have e2 : framePlus q 4 =
      (q ^ 6 - 1) * (q ^ 5 + 1) * q ^ 10 * ((q ^ 5 - 1) * (q ^ 4 + 1) * q ^ 8) := rfl
  rw [e1, e2] at h
  have hq4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have hq5' : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq1
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  zify [hq4, hq5', hq6] at h
  have hqz : (5 : ℤ) ≤ q := by exact_mod_cast hq5
  have h0 : -2 * (q : ℤ) ^ 22 * ((q : ℤ) ^ 10 - 1) * ((q : ℤ) ^ 2 - 1) = 0 := by
    linear_combination h
  have hq2z : (0 : ℤ) < (q : ℤ) ^ 2 - 1 := by nlinarith
  have hq10z : (0 : ℤ) < (q : ℤ) ^ 10 - 1 := by
    have : (1 : ℤ) < (q : ℤ) ^ 10 := one_lt_pow₀ (by omega) (by norm_num)
    linarith
  have hpos : (0 : ℤ) < (q : ℤ) ^ 22 * ((q : ℤ) ^ 10 - 1) * ((q : ℤ) ^ 2 - 1) :=
    mul_pos (mul_pos (pow_pos (by omega) 22) hq10z) hq2z
  linarith

end Compare

end CFSG.ClassicalInvolution.ModelFacts.E8D8
