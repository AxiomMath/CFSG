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

namespace CFSG.Evidence

open Equiv

namespace TimmRefute

@[expose] def x3 (a b c : Fin 8) : Fin 8 := a ^^^ b ^^^ c

@[expose] def IsAff (σ : Perm (Fin 8)) : Prop := ∀ a b c, σ (x3 a b c) = x3 (σ a) (σ b) (σ c)

instance : DecidablePred IsAff := fun σ => by unfold IsAff; infer_instance

@[expose] def AGL : Subgroup (Perm (Fin 8)) where
  carrier := {σ | IsAff σ}
  mul_mem' := by
    intro σ τ hσ hτ a b c
    change IsAff σ at hσ
    change IsAff τ at hτ
    rw [Perm.mul_apply, hτ, hσ]
    rfl
  one_mem' := fun _ _ _ => rfl
  inv_mem' := by
    intro σ hσ a b c
    change IsAff σ at hσ
    apply σ.injective
    rw [hσ]
    simp

theorem mem_AGL {σ : Perm (Fin 8)} : σ ∈ AGL ↔ IsAff σ := Iff.rfl

instance : DecidablePred (· ∈ AGL) := fun _ => decidable_of_iff _ mem_AGL.symm

@[expose] def t : AGL := ⟨swap 2 3 * swap 6 7, by decide⟩

@[expose] def Checks (U S L : Finset AGL) : Prop :=
  U.card = 1344 ∧
  (∀ d ∈ S, d ^ 2 = 1 ∧ d ≠ 1) ∧
  (∀ d ∈ S, ∀ e ∈ S, (d * e) ^ 3 = 1 ∨ ((d * e) ^ 2 = 1 ∧ d * e ≠ 1) ∨
    ((d * e) ^ 4 = 1 ∧ (d * e) ^ 2 ≠ 1)) ∧
  (∀ d ∈ S, ∀ e ∈ S, (d * e) ^ 4 = 1 → (d * e) ^ 2 ≠ 1 → (d * e) ^ 2 ∈ S) ∧
  (∃ d ∈ S, ∃ e ∈ S, (d * e) ^ 4 = 1 ∧ (d * e) ^ 2 ≠ 1) ∧
  (∀ z ∈ U, (∀ g ∈ U, g * z = z * g) → z = 1) ∧
  (∀ x ∈ U, x ≠ 1 → x ^ 21 = 1 → ∃ c ∈ U, (x * (c * x * c⁻¹)) ^ 21 ≠ 1) ∧
  (∀ g ∈ U, ∃ d₁ ∈ S, ∃ d₂ ∈ S, ((d₁ * d₂)⁻¹ * g).1 0 = 0) ∧
  (∀ M ∈ U, M.1 0 = 0 → ∃ a ∈ L, ∃ b ∈ L, ∃ c ∈ L, M = a * b * c)

section

attribute [local instance 10000] Finset.decidableDforallFinset

set_option synthInstance.maxSize 4096 in
instance (U S L : Finset AGL) : Decidable (Checks U S L) := by
  unfold Checks; infer_instance

end

end TimmRefute

end CFSG.Evidence
