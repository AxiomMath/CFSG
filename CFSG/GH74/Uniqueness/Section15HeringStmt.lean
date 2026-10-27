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
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
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

namespace CFSG.GH74.Uniqueness

@[expose] def Hering32Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Γ : Type) [MulAction G Γ] [FaithfulSMul G Γ] (m : ℕ),
    2 ≤ m → ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ m → ∀ (e : Γ ≃ F),
    MulAction.IsMultiplyPretransitive G Γ 2 →
    (∀ g : G, g • e.symm 0 = e.symm 0 →
      ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x : F, e (g • e.symm x) = a * σ x) →
    (∀ a : Fˣ, ∃ g : G, g • e.symm 0 = e.symm 0 ∧ ∀ x : F, e (g • e.symm x) = a * x) →
    (∃ N : Subgroup G, N.Normal ∧ ∀ γ δ : Γ, ∃! n : N, (n : G) • γ = δ) ∨
      (m = 3 ∧ Nonempty (G ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))

end CFSG.GH74.Uniqueness
