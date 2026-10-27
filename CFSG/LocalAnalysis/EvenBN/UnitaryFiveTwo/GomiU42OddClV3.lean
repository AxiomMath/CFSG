module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem u42_factorization_three_pow_sub_pow {f k i : ℕ} (hf : 1 ≤ f) (hik : i < k) :
    ((3 ^ f) ^ k - (3 ^ f) ^ i).factorization 3 = f * i := by
  have hlt : 1 < (3 ^ f) ^ (k - i) :=
    Nat.one_lt_pow (by omega) (Nat.one_lt_pow (by omega) (by norm_num))
  have hq : (3 ^ f) ^ k - (3 ^ f) ^ i = (3 ^ f) ^ i * ((3 ^ f) ^ (k - i) - 1) := by
    have h1 : (3 ^ f) ^ k = (3 ^ f) ^ i * (3 ^ f) ^ (k - i) := by
      rw [← pow_add]; congr 1; omega
    rw [h1, Nat.mul_sub, mul_one]
  have hne1 : (3 ^ f) ^ (k - i) - 1 ≠ 0 := by omega
  have hne2 : (3 ^ f) ^ i ≠ 0 := by positivity
  have hndvd : ¬ 3 ∣ (3 ^ f) ^ (k - i) - 1 := by
    intro h3
    have h4 : 3 ∣ (3 ^ f) ^ (k - i) :=
      dvd_pow (dvd_pow_self 3 (by omega)) (by omega)
    have h5 : 3 ∣ (3 ^ f) ^ (k - i) - ((3 ^ f) ^ (k - i) - 1) := Nat.dvd_sub h4 h3
    have h6 : (3 ^ f) ^ (k - i) - ((3 ^ f) ^ (k - i) - 1) = 1 := by omega
    rw [h6] at h5
    omega
  rw [hq, Nat.factorization_mul hne2 hne1, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp [mul_comm]

theorem u42_factorization_three_prod_GL {f : ℕ} (hf : 1 ≤ f) (k : ℕ) :
    (∏ i : Fin k, ((3 ^ f) ^ k - (3 ^ f) ^ (i : ℕ))).factorization 3 = f * (k * (k - 1) / 2) := by
  rw [Nat.factorization_prod (fun i _ => by
      have : (3 ^ f) ^ (i : ℕ) < (3 ^ f) ^ k :=
        Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by norm_num)) i.2
      omega)]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => u42_factorization_three_pow_sub_pow hf i.2)]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => i) k, Finset.sum_range_id]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
