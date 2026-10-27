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
public import Std.Tactic.BVDecide.Normalize.Prop

public section
set_option linter.unusedSectionVars false
namespace CFSG.ClassicalInvolution.Asc77
namespace T8X

theorem exists_four_gen {α : Type*} {C : Set α} (hC : C.ncard = 4) {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ c d : α, C = {a, b, c, d} ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b := by
  have hsub : ({a, b} : Set α) ⊆ C := by
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have h2 : (C \ {a, b}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub (Set.toFinite _), hC, Set.ncard_pair hab]
  obtain ⟨c, d, hcd, hcd'⟩ := Set.ncard_eq_two.mp h2
  have hcm : c ∈ C \ {a, b} := by rw [hcd']; simp
  have hdm : d ∈ C \ {a, b} := by rw [hcd']; simp
  refine ⟨c, d, ?_, hcd, ?_, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_cases hxab : x ∈ ({a, b} : Set α)
      · rcases hxab with rfl | rfl <;> simp
      · have : x ∈ C \ {a, b} := ⟨hx, hxab⟩
        rw [hcd'] at this
        rcases this with rfl | rfl <;> simp
    · intro hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hcm.1
      · exact hdm.1
  · intro h; exact hcm.2 (by simp [h])
  · intro h; exact hcm.2 (by simp [h])
  · intro h; exact hdm.2 (by simp [h])
  · intro h; exact hdm.2 (by simp [h])

end T8X
end CFSG.ClassicalInvolution.Asc77
