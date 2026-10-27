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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.LieType.Seitz

variable {K : Type*} [Group K]

@[expose] def fixedPoints (F : Subgroup (MulAut K)) : Subgroup K where
  carrier := {k | ∀ φ ∈ F, φ k = k}
  one_mem' := fun φ _ => map_one φ
  mul_mem' := fun ha hb φ hφ => by rw [map_mul, ha φ hφ, hb φ hφ]
  inv_mem' := fun ha φ hφ => by rw [map_inv, ha φ hφ]

@[expose] def seitzGamma (E : Subgroup (MulAut K)) : Subgroup K :=
  ⨆ (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F ≠ ⊥), fixedPoints F

@[expose] def seitzHyperGamma (p : ℕ) (E : Subgroup (MulAut K)) : Subgroup K :=
  ⨆ (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p), fixedPoints F

theorem mem_fixedPoints {F : Subgroup (MulAut K)} {k : K} : k ∈ fixedPoints F ↔ ∀ φ ∈ F, φ k = k :=
  Iff.rfl

end CFSG.LieType.Seitz
