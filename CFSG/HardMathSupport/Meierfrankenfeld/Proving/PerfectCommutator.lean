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

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving

variable {X : Type*} [Group X]

theorem commutator_eq_bot_of_isPerfect {L J : Subgroup X} (hL : ⁅L, L⁆ = L)
    (h : ⁅⁅L, J⁆, L⁆ = ⊥) : ⁅L, J⁆ = ⊥ := by
  have hJL : ⁅⁅J, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (H₁ := J) (H₂ := L)]
    exact h
  have key := Subgroup.commutator_commutator_eq_bot_of_rotate h hJL
  rwa [hL] at key

theorem le_centralizer_of_isPerfect {L J : Subgroup X} (hL : ⁅L, L⁆ = L)
    (h : ⁅⁅L, J⁆, L⁆ = ⊥) : J ≤ Subgroup.centralizer (L : Set X) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  rw [Subgroup.commutator_comm (H₁ := J) (H₂ := L)]
  exact commutator_eq_bot_of_isPerfect hL h

end CFSG.HardMathSupport.Meierfrankenfeld.Proving
