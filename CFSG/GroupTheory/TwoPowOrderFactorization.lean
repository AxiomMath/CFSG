module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.GroupTheory

theorem factorization_pow_add_one_eq_zero {q r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hq : q ≡ 1 [MOD r]) : (q ^ k + 1).factorization r = 0 := by
  refine Nat.factorization_eq_zero_of_not_dvd ?_
  have h2 : q ^ k + 1 ≡ 2 [MOD r] := by
    have := (hq.pow k).add (Nat.ModEq.refl 1)
    simpa using this
  intro hd
  have h0 : q ^ k + 1 ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr hd
  have h20 : (2 : ℕ) ≡ 0 [MOD r] := h2.symm.trans h0
  have hdvd2 : r ∣ 2 := Nat.modEq_zero_iff_dvd.mp h20
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp hdvd2)

theorem not_dvd_of_modEq_one_of_prime {q r : ℕ} (hr : r.Prime) (hq : q ≡ 1 [MOD r]) :
    ¬ r ∣ q := by
  intro h
  have h0 : q ≡ 0 [MOD r] := Nat.modEq_zero_iff_dvd.mpr h
  have h1 : (1 : ℕ) ≡ 0 [MOD r] := hq.symm.trans h0
  exact hr.not_dvd_one (Nat.modEq_zero_iff_dvd.mp h1)

theorem factorization_card_L2 {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) :
    (q * (q ^ 2 - 1)).factorization r = (q - 1).factorization r := by
  have hq0 : q ≠ 0 := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm (q - 1) (q + 1), ← Nat.sq_sub_sq q 1, one_pow]
  have hp1 : q + 1 ≠ 0 := by positivity
  have hm1 : q - 1 ≠ 0 := by omega
  have hq2 : q ^ 2 - 1 ≠ 0 := by rw [hsq]; exact mul_ne_zero hm1 hp1
  have hqzero : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_modEq_one_of_prime hr hq)
  have hp1zero : (q + 1).factorization r = 0 := by
    simpa using factorization_pow_add_one_eq_zero (k := 1) hr hr2 hq
  rw [Nat.factorization_mul hq0 hq2, Finsupp.add_apply, hsq,
    Nat.factorization_mul hm1 hp1, Finsupp.add_apply, hqzero, hp1zero]
  ring

theorem factorization_card_Sp4 {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) :
    (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))).factorization r
      = 2 * (q - 1).factorization r := by
  have hq0 : q ≠ 0 := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm (q - 1) (q + 1), ← Nat.sq_sub_sq q 1, one_pow]
  have hsq4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, mul_comm (q ^ 2 - 1) (q ^ 2 + 1),
      ← Nat.sq_sub_sq (q ^ 2) 1, one_pow]
  have hp1 : q + 1 ≠ 0 := by positivity
  have hm1 : q - 1 ≠ 0 := by omega
  have hq2p1 : q ^ 2 + 1 ≠ 0 := by positivity
  have hq2 : q ^ 2 - 1 ≠ 0 := by rw [hsq]; exact mul_ne_zero hm1 hp1
  have hq4 : q ^ 4 - 1 ≠ 0 := by rw [hsq4]; exact mul_ne_zero hq2 hq2p1
  have hq4q : q ^ 4 ≠ 0 := by positivity
  have hqzero : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_modEq_one_of_prime hr hq)
  have hp1zero : (q + 1).factorization r = 0 := by
    simpa using factorization_pow_add_one_eq_zero (k := 1) hr hr2 hq
  have hq2p1zero : (q ^ 2 + 1).factorization r = 0 :=
    factorization_pow_add_one_eq_zero (k := 2) hr hr2 hq
  have hq4zero : (q ^ 4).factorization r = 0 := by
    rw [Nat.factorization_pow]
    simp [hqzero]
  rw [Nat.factorization_mul hq4q (mul_ne_zero hq2 hq4), Finsupp.add_apply,
    Nat.factorization_mul hq2 hq4, Finsupp.add_apply, hq4zero, hsq4,
    Nat.factorization_mul hq2 hq2p1, Finsupp.add_apply, hsq,
    Nat.factorization_mul hm1 hp1, Finsupp.add_apply, hp1zero, hq2p1zero]
  ring

theorem factorization_card_U3 {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) :
    (q ^ 3 * (q ^ 3 + 1) * (q ^ 2 - 1)).factorization r = (q - 1).factorization r := by
  have hq0 : q ≠ 0 := by omega
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm (q - 1) (q + 1), ← Nat.sq_sub_sq q 1, one_pow]
  have hq3 : q ^ 3 ≠ 0 := by positivity
  have hq3p1 : q ^ 3 + 1 ≠ 0 := by positivity
  have hp1 : q + 1 ≠ 0 := by positivity
  have hm1 : q - 1 ≠ 0 := by omega
  have hq2 : q ^ 2 - 1 ≠ 0 := by rw [hsq]; exact mul_ne_zero hm1 hp1
  have hqzero : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_modEq_one_of_prime hr hq)
  have hq3zero : (q ^ 3).factorization r = 0 := by
    rw [Nat.factorization_pow]; simp [hqzero]
  have hq3p1zero : (q ^ 3 + 1).factorization r = 0 :=
    factorization_pow_add_one_eq_zero (k := 3) hr hr2 hq
  have hp1zero : (q + 1).factorization r = 0 := by
    simpa using factorization_pow_add_one_eq_zero (k := 1) hr hr2 hq
  rw [Nat.factorization_mul (mul_ne_zero hq3 hq3p1) hq2, Finsupp.add_apply,
    Nat.factorization_mul hq3 hq3p1, Finsupp.add_apply, hq3zero, hq3p1zero, zero_add,
    hsq, Nat.factorization_mul hm1 hp1, Finsupp.add_apply, hp1zero, add_zero]
  exact zero_add _

theorem factorization_card_L2Square {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) :
    (q ^ 2 * (q ^ 2 - 1) ^ 2).factorization r = 2 * (q - 1).factorization r := by
  have hq2 : q ^ 2 ≠ 0 := by positivity
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [mul_comm (q - 1) (q + 1), ← Nat.sq_sub_sq q 1, one_pow]
  have hp1 : q + 1 ≠ 0 := by positivity
  have hm1 : q - 1 ≠ 0 := by omega
  have hq2m1 : q ^ 2 - 1 ≠ 0 := by rw [hsq]; exact mul_ne_zero hm1 hp1
  have hqzero : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_modEq_one_of_prime hr hq)
  have hq2zero : (q ^ 2).factorization r = 0 := by
    rw [Nat.factorization_pow]; simp [hqzero]
  have hp1zero : (q + 1).factorization r = 0 := by
    simpa using factorization_pow_add_one_eq_zero (k := 1) hr hr2 hq
  have h1 : (q ^ 2 - 1).factorization r = (q - 1).factorization r := by
    rw [hsq, Nat.factorization_mul hm1 hp1, Finsupp.add_apply, hp1zero, add_zero]
  rw [Nat.factorization_mul hq2 (pow_ne_zero 2 hq2m1), Finsupp.add_apply, hq2zero,
    Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul, h1]
  ring

theorem factorization_card_Sz {q r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) :
    (q ^ 2 * (q ^ 2 + 1) * (q - 1)).factorization r = (q - 1).factorization r := by
  have hq2 : q ^ 2 ≠ 0 := by positivity
  have hq2p1 : q ^ 2 + 1 ≠ 0 := by positivity
  have hm1 : q - 1 ≠ 0 := by omega
  have hqzero : q.factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_modEq_one_of_prime hr hq)
  have hq2zero : (q ^ 2).factorization r = 0 := by
    rw [Nat.factorization_pow]; simp [hqzero]
  have hq2p1zero : (q ^ 2 + 1).factorization r = 0 :=
    factorization_pow_add_one_eq_zero (k := 2) hr hr2 hq
  rw [Nat.factorization_mul (mul_ne_zero hq2 hq2p1) hm1, Finsupp.add_apply,
    Nat.factorization_mul hq2 hq2p1, Finsupp.add_apply, hq2zero, hq2p1zero]
  simp

theorem not_dvd_gcd_three_add_one {q r : ℕ} (hr : r.Prime) (h2q : 2 ≤ q)
    (hq : q ≡ 1 [MOD r]) : ¬ r ∣ Nat.gcd 3 (q + 1) := by
  intro h
  have h3 : r ∣ 3 := (Nat.dvd_gcd_iff.mp h).1
  have hq1 : r ∣ q + 1 := (Nat.dvd_gcd_iff.mp h).2
  have hr3 : r = 3 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3
  have hqm1 : r ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).mp hq.symm
  have h2 : r ∣ 2 := by
    have hsub : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hq1 hqm1
    rwa [show q + 1 - (q - 1) = 2 by omega] at hsub
  rw [hr3] at h2
  norm_num at h2

end CFSG.GroupTheory
