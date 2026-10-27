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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisQuot

theorem trace_mat_conj (c x : latticeO) : (mat (c * x * c⁻¹)).trace = (mat x).trace := by
  rw [mat_mul, mat_mul, Matrix.trace_mul_comm (mat c * mat x), ← mul_assoc, ← mat_mul,
    inv_mul_cancel, mat_one, one_mul]

theorem trace_mat_gO (b : C) :
    (mat (gO b)).trace = 24 - 2 * (hammingNorm (b : Fin 24 → ZMod 2) : ℚ) := by
  rw [mat_gO, gmat, Matrix.trace_diagonal]
  have h : ∀ i, CFSG.Monster.sgn ((b : Fin 24 → ZMod 2) i) =
      1 - 2 * (if (b : Fin 24 → ZMod 2) i ≠ 0 then (1 : ℚ) else 0) := by
    intro i
    unfold CFSG.Monster.sgn
    split_ifs <;> simp_all
    norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hammingNorm, Finset.natCast_card_filter]
  simp

theorem trace_mat_negOneO : (mat negOneO).trace = -24 := by
  rw [mat_negOneO]
  simp

end CFSG.EvenSporadicStandard.TwoCo1
