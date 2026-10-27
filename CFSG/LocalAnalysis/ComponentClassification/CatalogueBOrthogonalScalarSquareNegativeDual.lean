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
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
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

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative

variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

@[expose] def inverseDualAction (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f : U ≃ₗ[K] U) : W ≃ₗ[K] W :=
  (p.flip.toPerfPair.trans f.symm.dualMap).trans p.flip.toPerfPair.symm

theorem inverseDualAction_pairing (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f : U ≃ₗ[K] U) (x : U) (y : W) :
    p x (inverseDualAction p f y) = p (f.symm x) y := by
  simp [inverseDualAction, LinearEquiv.trans_apply]

theorem inverseDualAction_preserves (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f : U ≃ₗ[K] U) (x : U) (y : W) :
    p (f x) (inverseDualAction p f y) = p x y := by
  rw [inverseDualAction_pairing, f.symm_apply_apply]

theorem inverseDualAction_unique (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f : U ≃ₗ[K] U) (g : W ≃ₗ[K] W)
    (hg : ∀ x y, p (f x) (g y) = p x y) : g = inverseDualAction p f := by
  ext y
  apply p.flip.toPerfPair.injective
  ext x
  change p x (g y) = p x (inverseDualAction p f y)
  rw [inverseDualAction_pairing]
  simpa only [f.apply_symm_apply] using hg (f.symm x) y

theorem inverseDualAction_one (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair] :
    inverseDualAction p (1 : U ≃ₗ[K] U) = 1 := by
  symm
  apply inverseDualAction_unique
  intro x y
  rfl

theorem inverseDualAction_mul (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f g : U ≃ₗ[K] U) :
    inverseDualAction p (f * g) = inverseDualAction p f * inverseDualAction p g := by
  symm
  apply inverseDualAction_unique
  intro x y
  change p (f (g x)) (inverseDualAction p f (inverseDualAction p g y)) = p x y
  rw [inverseDualAction_preserves, inverseDualAction_preserves]

@[expose] def inverseDualHom (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair] :
    (U ≃ₗ[K] U) →* (W ≃ₗ[K] W) where
  toFun := inverseDualAction p
  map_one' := inverseDualAction_one p
  map_mul' := inverseDualAction_mul p

theorem inverseDualAction_inv (p : U →ₗ[K] W →ₗ[K] K) [p.IsPerfPair]
    (f : U ≃ₗ[K] U) : inverseDualAction p f⁻¹ = (inverseDualAction p f)⁻¹ :=
  (inverseDualHom p).map_inv f

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquareNegative
