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

namespace CFSG.DisconnectedInvolutionGraph.Helpers

theorem odd_card_of_involution_unique_fixed_point {α : Type*} [Finite α]
    (permutation : Equiv.Perm α) (hsquare : permutation ^ 2 = 1)
    (hfixed : ∃! point : α, permutation point = point) : Odd (Nat.card α) := by
  classical
  let _ := Fintype.ofFinite α
  obtain ⟨point, hpoint, hunique⟩ := hfixed
  have hcompl : permutation.supportᶜ = {point} := by
    ext other
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not,
      Finset.mem_singleton]
    exact ⟨fun hother => hunique other hother, fun heq => heq ▸ hpoint⟩
  have hcard := Finset.card_compl_add_card permutation.support
  rw [hcompl, Finset.card_singleton, Fintype.card_eq_nat_card] at hcard
  have heven := even_iff_two_dvd.mpr (Equiv.Perm.two_dvd_card_support hsquare)
  obtain ⟨half, hhalf⟩ := heven
  exact ⟨half, by omega⟩

end CFSG.DisconnectedInvolutionGraph.Helpers
