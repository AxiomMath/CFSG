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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
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

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev X : Type := Fin 6 → ZMod 2

@[expose] def polarQ (x y : X) : ZMod 2 :=
  x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1 + x 4 * y 5 + x 5 * y 4

@[expose] def polarQBilin : LinearMap.BilinForm (ZMod 2) X :=
  LinearMap.mk₂ (ZMod 2) polarQ
    (fun _ _ _ => by simp only [polarQ, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [polarQ, Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [polarQ, Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [polarQ, Pi.smul_apply, smul_eq_mul]; ring)

@[expose] def Q : QuadraticForm (ZMod 2) X where
  toFun x := x 0 * x 2 + x 1 * x 3 + x 4 ^ 2 + x 4 * x 5 + x 5 ^ 2
  toFun_smul a x := by simp only [Pi.smul_apply, smul_eq_mul]; ring
  exists_companion' := ⟨polarQBilin, fun x y => by
    have h2 : (2 : ZMod 2) = 0 := rfl
    simp only [polarQBilin, LinearMap.mk₂_apply, polarQ, Pi.add_apply]
    linear_combination (x 4 * y 4 + x 5 * y 5) * h2⟩

theorem Q_apply (x : X) : Q x = x 0 * x 2 + x 1 * x 3 + x 4 ^ 2 + x 4 * x 5 + x 5 ^ 2 := rfl

theorem polar_Q (x y : X) : QuadraticMap.polar Q x y = polarQ x y := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [QuadraticMap.polar, Q_apply, polarQ, Pi.add_apply]
  linear_combination (x 4 * y 4 + x 5 * y 5) * h2

@[expose] def e₁ : X := Pi.single 0 1

@[expose] def e₂ : X := Pi.single 1 1

@[expose] def f₁ : X := Pi.single 2 1

@[expose] def f₂ : X := Pi.single 3 1

@[expose] def IsTotallySingular (U : Submodule (ZMod 2) X) : Prop :=
  ∀ x ∈ U, Q x = 0

abbrev QVertex : Type :=
  {U : Submodule (ZMod 2) X //
    IsTotallySingular U ∧ (finrank (ZMod 2) U = 1 ∨ finrank (ZMod 2) U = 2)}

@[expose] def QVertex.Incident (x y : QVertex) : Prop :=
  x.1 ≤ y.1 ∨ y.1 ≤ x.1

@[expose] noncomputable def QVertex.type (x : QVertex) : ℕ :=
  finrank (ZMod 2) x.1

end CFSG.LieType.Chevalley.C2E6Overlap
