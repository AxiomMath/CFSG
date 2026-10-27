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

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

@[expose] def kleinFourPerm : Subgroup (Perm (Fin 4)) where
  carrier := {σ | σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨
    σ = swap 0 3 * swap 1 2}
  mul_mem' := by
    have h : ∀ a b : Perm (Fin 4),
        (a = 1 ∨ a = swap 0 1 * swap 2 3 ∨ a = swap 0 2 * swap 1 3 ∨ a = swap 0 3 * swap 1 2) →
        (b = 1 ∨ b = swap 0 1 * swap 2 3 ∨ b = swap 0 2 * swap 1 3 ∨ b = swap 0 3 * swap 1 2) →
        (a * b = 1 ∨ a * b = swap 0 1 * swap 2 3 ∨ a * b = swap 0 2 * swap 1 3 ∨
          a * b = swap 0 3 * swap 1 2) := by decide
    exact fun {a b} ha hb => h a b ha hb
  one_mem' := Or.inl rfl
  inv_mem' := by
    have h : ∀ a : Perm (Fin 4),
        (a = 1 ∨ a = swap 0 1 * swap 2 3 ∨ a = swap 0 2 * swap 1 3 ∨ a = swap 0 3 * swap 1 2) →
        (a⁻¹ = 1 ∨ a⁻¹ = swap 0 1 * swap 2 3 ∨ a⁻¹ = swap 0 2 * swap 1 3 ∨
          a⁻¹ = swap 0 3 * swap 1 2) := by decide
    exact fun {a} ha => h a ha

instance : kleinFourPerm.Normal where
  conj_mem := by
    have h : ∀ n g : Perm (Fin 4),
        (n = 1 ∨ n = swap 0 1 * swap 2 3 ∨ n = swap 0 2 * swap 1 3 ∨ n = swap 0 3 * swap 1 2) →
        (g * n * g⁻¹ = 1 ∨ g * n * g⁻¹ = swap 0 1 * swap 2 3 ∨ g * n * g⁻¹ = swap 0 2 * swap 1 3 ∨
          g * n * g⁻¹ = swap 0 3 * swap 1 2) := by decide
    exact fun n hn g => h n g hn

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
