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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19C

open scoped MatrixGroups

theorem card_sl2 (F : Type) [Field F] [Finite F] :
    Nat.card SL(2, F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card F ^ 2 - Fintype.card F =
      Fintype.card F * (Fintype.card F - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem eight_dvd_sq_sub_one {m : ℕ} (hm : Odd m) : 8 ∣ m ^ 2 - 1 := by
  obtain ⟨j, rfl⟩ := hm
  have h : (2 * j + 1) ^ 2 - 1 = 4 * (j * (j + 1)) := by
    rw [Nat.sub_eq_of_eq_add]
    ring
  rw [h]
  obtain ⟨i, hi⟩ := Nat.even_mul_succ_self j
  rw [hi]
  exact ⟨i, by ring⟩

theorem factorization_two_mul_sq_sub_one {m : ℕ} (hm : Odd m) :
    (m * (m ^ 2 - 1)).factorization 2 = (m ^ 2 - 1).factorization 2 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
  have h1 : 1 < m ^ 2 ∨ m = 1 := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact Or.inl (by nlinarith)
    · exact Or.inr (by omega)
  rcases h1 with h1 | rfl
  · have h2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
    rw [Nat.factorization_mul hm0 (by omega), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h2, zero_add]
  · simp

theorem factorization_two_sq_sq_sub_one {m : ℕ} (hm : Odd m) (hm1 : 1 < m) :
    ((m ^ 2) ^ 2 - 1).factorization 2 = (m ^ 2 - 1).factorization 2 + 1 := by
  obtain ⟨i, hi⟩ := eight_dvd_sq_sub_one hm
  have hm2 : 1 < m ^ 2 := by nlinarith
  have e1 : (m ^ 2) ^ 2 - 1 = (m ^ 2 - 1) * (2 * (4 * i + 1)) := by
    have h2 : m ^ 2 = 8 * i + 1 := by omega
    rw [h2]
    rw [Nat.sub_eq_of_eq_add]
    rw [show 8 * i + 1 - 1 = 8 * i by omega]
    ring
  rw [e1, Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * i + 1)]

variable {p : ℕ} [Fact p.Prime]

theorem three_le_factorization_two_card_sl2 (hp2 : p ≠ 2) {e : ℕ} (he : e ≠ 0) :
    3 ≤ (Nat.card SL(2, GaloisField p e)).factorization 2 := by
  have hm : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two (Fact.out) hp2).pow
  have hm1 : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  rw [card_sl2, GaloisField.card p e he, factorization_two_mul_sq_sub_one hm]
  have h8 := eight_dvd_sq_sub_one hm
  have hne : (p ^ e) ^ 2 - 1 ≠ 0 := by
    have : 1 < (p ^ e) ^ 2 := by nlinarith
    omega
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp (by simpa using h8)

theorem factorization_two_card_sl2_two_mul (hp2 : p ≠ 2) {e : ℕ} (he : e ≠ 0) :
    (Nat.card SL(2, GaloisField p (2 * e))).factorization 2 =
      (Nat.card SL(2, GaloisField p e)).factorization 2 + 1 := by
  have hm : Odd (p ^ e) := (Nat.Prime.odd_of_ne_two (Fact.out) hp2).pow
  have hm1 : 1 < p ^ e := Nat.one_lt_pow he (Fact.out : p.Prime).one_lt
  rw [card_sl2, card_sl2, GaloisField.card p e he, GaloisField.card p (2 * e) (by omega),
    show p ^ (2 * e) = (p ^ e) ^ 2 by rw [← pow_mul, mul_comm],
    factorization_two_mul_sq_sub_one hm, factorization_two_mul_sq_sub_one hm.pow,
    factorization_two_sq_sq_sub_one hm hm1]

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19C
