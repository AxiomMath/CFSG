module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup

section Elements

variable {G : Type} [Group G] [Finite G]

theorem exists_two_mul_mem_zpowers_sq (k : G) :
    ∃ y ∈ zpowers k, IsPGroup 2 (zpowers y) ∧ ∃ z ∈ zpowers (k ^ 2), k = y * z := by
  have hn : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ e) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set a := Nat.gcdA (2 ^ e) m
  set b := Nat.gcdB (2 ^ e) m
  refine ⟨k ^ ((m : ℤ) * b), zpow_mem (mem_zpowers k) _, ?_, k ^ ((2 : ℤ) ^ e * a), ?_, ?_⟩
  ·
    have hdvd : orderOf (k ^ ((m : ℤ) * b)) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * b * ((2 ^ e : ℕ) : ℤ) =
        ((2 ^ e * m : ℕ) : ℤ) * b by push_cast; ring, ← hnm, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  ·
    rcases e with _ | e
    ·
      have hodd : Odd (orderOf k) := by rw [hnm]; simpa using hm
      obtain ⟨j, hj⟩ := hodd
      have hk : k ∈ zpowers (k ^ 2) := by
        refine ⟨((j + 1 : ℕ) : ℤ), ?_⟩
        simp only [zpow_natCast]
        rw [← pow_mul, show 2 * (j + 1) = orderOf k + 1 by omega, pow_succ, pow_orderOf_eq_one,
          one_mul]
      exact zpow_mem ((zpowers_le.mpr hk) (mem_zpowers k)) _
    · refine ⟨(2 : ℤ) ^ e * a, ?_⟩
      simp only
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
  · rw [← zpow_add, show (m : ℤ) * b + 2 ^ e * a = 1 by rw [hbez]; push_cast; ring, zpow_one]

theorem exists_two_mul_odd (k : G) :
    ∃ y ∈ zpowers k, IsPGroup 2 (zpowers y) ∧ ∃ w ∈ zpowers k, Odd (orderOf w) ∧ k = y * w := by
  have hn : orderOf k ≠ 0 := (orderOf_pos k).ne'
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : Nat.Coprime (2 ^ e) m := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm)
  have hbez := Nat.gcd_eq_gcd_ab (2 ^ e) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  set a := Nat.gcdA (2 ^ e) m
  set b := Nat.gcdB (2 ^ e) m
  refine ⟨k ^ ((m : ℤ) * b), zpow_mem (mem_zpowers k) _, ?_, k ^ ((2 : ℤ) ^ e * a),
    zpow_mem (mem_zpowers k) _, ?_, ?_⟩
  · have hdvd : orderOf (k ^ ((m : ℤ) * b)) ∣ 2 ^ e := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * b * ((2 ^ e : ℕ) : ℤ) =
        ((2 ^ e * m : ℕ) : ℤ) * b by push_cast; ring, ← hnm, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  · have hdvd : orderOf (k ^ ((2 : ℤ) ^ e * a)) ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← zpow_natCast, ← zpow_mul, show (2 : ℤ) ^ e * a * (m : ℤ) =
        ((2 ^ e * m : ℕ) : ℤ) * a by push_cast; ring, ← hnm, zpow_mul, zpow_natCast,
        pow_orderOf_eq_one, one_zpow]
    exact hm.of_dvd_nat hdvd
  · rw [← zpow_add, show (m : ℤ) * b + 2 ^ e * a = 1 by rw [hbez]; push_cast; ring, zpow_one]

end Elements

end CFSG.ComponentClassification.AS81
