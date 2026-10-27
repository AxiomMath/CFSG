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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

theorem trace_pi_component_operator {index : Type*} [Fintype index]
    (vector : index → Type*) [∀ label, AddCommGroup (vector label)]
    [∀ label, Module ℂ (vector label)] [∀ label, FiniteDimensional ℂ (vector label)]
    (operator : Module.End ℂ (∀ label, vector label))
    (component : ∀ label, Module.End ℂ (vector label))
    (haction : ∀ function label, operator function label = component label (function label)) :
    LinearMap.trace ℂ (∀ label, vector label) operator =
      ∑ label, LinearMap.trace ℂ (vector label) (component label) := by
  classical
  let basis := fun label => Module.finBasis ℂ (vector label)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis basis)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sigma, LinearMap.toMatrix_apply,
    Pi.basis_repr, Pi.basis_apply, haction, Pi.single_eq_same]
  apply Finset.sum_congr rfl
  intro label _
  rw [LinearMap.trace_eq_matrix_trace ℂ (basis label)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]

theorem trace_pi_coordinate_operator {index vector : Type*} [Fintype index] [DecidableEq index]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (operator : Module.End ℂ (index → vector)) (coordinate : index → index)
    (component : index → Module.End ℂ vector)
    (haction : ∀ function label, operator function label =
      component label (function (coordinate label))) :
    LinearMap.trace ℂ (index → vector) operator =
      ∑ label, if coordinate label = label then LinearMap.trace ℂ vector (component label)
        else 0 := by
  classical
  let basis := Module.finBasis ℂ vector
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _label : index => basis)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sigma, LinearMap.toMatrix_apply,
    Pi.basis_repr, Pi.basis_apply]
  apply Finset.sum_congr rfl
  intro label _
  by_cases hfixed : coordinate label = label
  · simp only [hfixed, ite_eq_left, haction, Pi.single_eq_same]
    rw [LinearMap.trace_eq_matrix_trace ℂ basis]
    simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  · simp [haction, hfixed]

end CFSG.TwoRankLowerBound.Helpers
