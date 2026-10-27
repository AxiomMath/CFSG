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
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def orthogonalSubmoduleCongr (Q : QuadraticForm K V)
    (U W : Submodule K V) (h : U = W) :
    TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype) ≃*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype) := by
  subst W
  exact MulEquiv.refl _

theorem orthogonalSubmoduleCongr_apply (Q : QuadraticForm K V)
    (U W : Submodule K V) (h : U = W)
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp U.subtype)) (x : W) :
    ((orthogonalSubmoduleCongr Q U W h g).val x).val =
      (g.val (LinearEquiv.ofEq W U h.symm x)).val := by
  subst W
  rfl

theorem orthogonalSubmoduleCongr_symm_apply (Q : QuadraticForm K V)
    (U W : Submodule K V) (h : U = W)
    (g : TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) (x : U) :
    (((orthogonalSubmoduleCongr Q U W h).symm g).val x).val =
      (g.val (LinearEquiv.ofEq U W h x)).val := by
  subst W
  rfl

@[expose] def linearSubmoduleCongr (U W : Submodule K V) (h : U = W) :
    (U ≃ₗ[K] U) ≃* (W ≃ₗ[K] W) := by
  subst W
  exact MulEquiv.refl _

theorem linearSubmoduleCongr_apply (U W : Submodule K V) (h : U = W)
    (g : U ≃ₗ[K] U) (x : W) :
    (linearSubmoduleCongr U W h g x).val =
      (g (LinearEquiv.ofEq W U h.symm x)).val := by
  subst W
  rfl

theorem linearSubmoduleCongr_symm_apply (U W : Submodule K V) (h : U = W)
    (g : W ≃ₗ[K] W) (x : U) :
    ((linearSubmoduleCongr U W h).symm g x).val =
      (g (LinearEquiv.ofEq U W h x)).val := by
  subst W
  rfl

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
