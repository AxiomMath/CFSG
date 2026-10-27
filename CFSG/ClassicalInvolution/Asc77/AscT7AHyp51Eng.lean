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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T7AHyp51Eng

variable {G : Type} [Group G]

theorem eq_one_or_eq_of_mem_zpowers_gen
    {a x : G} (ha : orderOf a = 2) (hx : x ∈ Subgroup.zpowers a)
    : x = 1 ∨ x = a := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : a ^ (i % (orderOf a : ℤ)) = a ^ i := zpow_mod_orderOf a i
  rw [← h1, ha]
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem commutes_closure_gen
    {s : Set G} (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  have h1 : ∀ x ∈ Subgroup.closure s, ∀ b ∈ s, x * b = b * x := by
    intro x hx b hb
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h x hx b hb
    | one => simp
    | mul x y _ _ ihx ihy =>
      calc x * y * b = x * (y * b) := by group
        _ = x * (b * y) := by rw [ihy]
        _ = (x * b) * y := by group
        _ = (b * x) * y := by rw [ihx]
        _ = b * (x * y) := by group
    | inv x _ ihx =>
      have : b * x⁻¹ = x⁻¹ * b := by
        calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
          _ = x⁻¹ * (b * x) * x⁻¹ := by rw [ihx]
          _ = x⁻¹ * b := by group
      exact this.symm
  intro x hx y hy
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact h1 x hx y hy
  | one => simp
  | mul y y' _ _ ihy ihy' =>
    calc x * (y * y') = (x * y) * y' := by group
      _ = (y * x) * y' := by rw [ihy]
      _ = y * (x * y') := by group
      _ = y * (y' * x) := by rw [ihy']
      _ = (y * y') * x := by group
  | inv y _ ihy =>
    have : x * y⁻¹ = y⁻¹ * x := by
      calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by group
        _ = y⁻¹ * (x * y) * y⁻¹ := by rw [ihy]
        _ = y⁻¹ * x := by group
    exact this

theorem sq_closure_gen
    {s : Set G} (hs : ∀ a ∈ s, a * a = 1) (h : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxy : y * x = x * y := (commutes_closure_gen h x hx y hy).symm
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy]; simp
  | inv x _ ihx =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ihx]; simp

end T7AHyp51Eng

end CFSG.ClassicalInvolution.Asc77
