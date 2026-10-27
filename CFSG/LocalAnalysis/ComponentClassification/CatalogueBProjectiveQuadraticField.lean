module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
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

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBProjectiveQuadratic

open Polynomial

variable {K : Type*} [Field K]

@[expose] def quadraticPolynomial (lambda : K) : K[X] := X ^ 2 - C lambda

theorem quadraticPolynomial_monic (lambda : K) : (quadraticPolynomial lambda).Monic :=
  monic_X_pow_sub_C lambda (by decide)

theorem quadraticPolynomial_natDegree (lambda : K) :
    (quadraticPolynomial lambda).natDegree = 2 :=
  natDegree_X_pow_sub_C

theorem quadraticPolynomial_irreducible (lambda : K) (hns : ¬ IsSquare lambda) :
    Irreducible (quadraticPolynomial lambda) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · simp [quadraticPolynomial_natDegree]
  · intro x hx
    have hroot : x ^ 2 - lambda = 0 := by
      simpa [Polynomial.IsRoot, quadraticPolynomial] using hx
    apply hns
    exact (isSquare_iff_exists_sq lambda).mpr ⟨x, (sub_eq_zero.mp hroot).symm⟩

abbrev extension (lambda : K) := AdjoinRoot (quadraticPolynomial lambda)

instance extensionIrreducible (lambda : K) [Fact (¬ IsSquare lambda)] :
    Fact (Irreducible (quadraticPolynomial lambda)) :=
  ⟨quadraticPolynomial_irreducible lambda Fact.out⟩

theorem extension_isField (lambda : K) (hns : ¬ IsSquare lambda) :
    IsField (extension lambda) :=
  AdjoinRoot.isField_iff_irreducible.mpr (quadraticPolynomial_irreducible lambda hns)

instance extensionFinite (lambda : K) : Module.Finite K (extension lambda) :=
  (quadraticPolynomial_monic lambda).finite_adjoinRoot

theorem extension_finrank (lambda : K) : Module.finrank K (extension lambda) = 2 := by
  rw [(AdjoinRoot.powerBasis' (quadraticPolynomial_monic lambda)).finrank]
  exact quadraticPolynomial_natDegree lambda

theorem extension_root_square (lambda : K) :
    AdjoinRoot.root (quadraticPolynomial lambda) ^ 2 =
      algebraMap K (extension lambda) lambda := by
  apply sub_eq_zero.mp
  calc
    AdjoinRoot.root (quadraticPolynomial lambda) ^ 2 -
        algebraMap K (extension lambda) lambda =
        AdjoinRoot.mk (quadraticPolynomial lambda) (quadraticPolynomial lambda) := by
          change (AdjoinRoot.mk _) X ^ 2 - (AdjoinRoot.mk _) (C lambda) = _
          rw [← map_pow, ← map_sub]
          rfl
    _ = 0 := AdjoinRoot.mk_self

end CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
