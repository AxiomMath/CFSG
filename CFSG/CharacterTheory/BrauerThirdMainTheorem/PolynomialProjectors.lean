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

open scoped Classical

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem exists_polynomial_projector {coefficientRing : Type*} [CommRing coefficientRing]
    {index : Type*} [Fintype index] (eigenvalues : index → coefficientRing)
    (selected : Set index)
    (hseparated : ∀ left ∈ selected, ∀ right ∉ selected,
      IsUnit (eigenvalues left - eigenvalues right)) :
    ∃ projector : Polynomial coefficientRing, ∀ entry,
      Polynomial.eval (eigenvalues entry) projector = if entry ∈ selected then 1 else 0 := by
  classical
  let selectedIndices := Finset.univ.filter (fun entry => entry ∈ selected)
  let rejectedIndices := Finset.univ.filter (fun entry => entry ∉ selected)
  let selectedPolynomial : Polynomial coefficientRing :=
    ∏ entry ∈ selectedIndices, (Polynomial.X - Polynomial.C (eigenvalues entry))
  let rejectedPolynomial : Polynomial coefficientRing :=
    ∏ entry ∈ rejectedIndices, (Polynomial.X - Polynomial.C (eigenvalues entry))
  have hcoprime : IsCoprime selectedPolynomial rejectedPolynomial := by
    apply IsCoprime.prod_left
    intro left hleft
    apply IsCoprime.prod_right
    intro right hright
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (hseparated left (Finset.mem_filter.mp hleft).2 right (Finset.mem_filter.mp hright).2)
  obtain ⟨selectedFactor, rejectedFactor, hidentity⟩ := hcoprime
  refine ⟨rejectedFactor * rejectedPolynomial, ?_⟩
  intro entry
  by_cases hselected : entry ∈ selected
  · have hzero : Polynomial.eval (eigenvalues entry) selectedPolynomial = 0 := by
      dsimp only [selectedPolynomial]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ entry, hselected⟩)
      simp
    have hevaluated := congrArg (Polynomial.eval (eigenvalues entry)) hidentity
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
      hzero, mul_zero, zero_add] at hevaluated
    rw [ite_eq_left hselected]
    simpa only [Polynomial.eval_mul] using hevaluated
  · have hzero : Polynomial.eval (eigenvalues entry) rejectedPolynomial = 0 := by
      dsimp only [rejectedPolynomial]
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ entry, hselected⟩)
      simp
    rw [ite_eq_right hselected, Polynomial.eval_mul, hzero, mul_zero]

end CFSG.BrauerThirdMainTheorem.Helpers
