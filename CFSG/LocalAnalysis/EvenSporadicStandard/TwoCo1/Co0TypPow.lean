module

public import CFSG.Monster.VisQuot.Monomial
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

@[expose] def powSumC (p : AutPerm) (b : C) (k : ℕ) : C :=
  ∑ j ∈ Finset.range k, (permC (p ^ j)).symm b

theorem powSumC_zero (p : AutPerm) (b : C) : powSumC p b 0 = 0 := by
  rw [powSumC, Finset.sum_range_zero]

theorem powSumC_succ (p : AutPerm) (b : C) (k : ℕ) :
    powSumC p b (k + 1) = powSumC p b k + (permC (p ^ k)).symm b := by
  rw [powSumC, Finset.sum_range_succ]
  rfl

theorem gO_mul_PO_pow (b : C) (p : AutPerm) (k : ℕ) :
    (gO b * PO p) ^ k = gO (powSumC p b k) * PO (p ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, powSumC_zero, gO_zero, PO_one, mul_one]
  | succ k ih =>
    rw [pow_succ, ih, powSumC_succ, gO_add]
    calc gO (powSumC p b k) * PO (p ^ k) * (gO b * PO p)
        = gO (powSumC p b k) * (PO (p ^ k) * gO b) * PO p := by simp only [mul_assoc]
      _ = gO (powSumC p b k) * (gO ((permC (p ^ k)).symm b) * PO (p ^ k)) * PO p := by
        rw [PO_mul_gO]
      _ = gO (powSumC p b k) * gO ((permC (p ^ k)).symm b) * (PO (p ^ k) * PO p) := by
        simp only [mul_assoc]
      _ = gO (powSumC p b k) * gO ((permC (p ^ k)).symm b) * PO (p ^ (k + 1)) := by
        rw [← PO_mul, ← pow_succ']

theorem pow_eq_one_of_gO_mul_PO_pow_eq_one {b : C} {p : AutPerm} {k : ℕ}
    (h : (gO b * PO p) ^ k = 1) : p ^ k = 1 := by
  rw [gO_mul_PO_pow] at h
  have h1 : gO (powSumC p b k) * PO (p ^ k) = gO 0 * PO 1 := by
    rw [h, gO_zero, PO_one, mul_one]
  exact (gO_mul_PO_inj h1).2

end CFSG.EvenSporadicStandard.TwoCo1
