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

namespace CFSG.Certificates

variable {α : Type*}

theorem card_mul_card_inf_stabilizer_le [Finite α] (K : Subgroup (Equiv.Perm α)) (b : α)
    (S : Finset α) (hS : ∀ p ∈ S, ∃ g ∈ K, g b = p) :
    S.card * Nat.card ↥(K ⊓ MulAction.stabilizer (Equiv.Perm α) b) ≤ Nat.card K := by
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K b), Nat.card_prod]
  apply Nat.mul_le_mul
  · have hsub : (S : Set α) ⊆ MulAction.orbit K b := by
      intro p hp
      obtain ⟨g, hg, rfl⟩ := hS p hp
      exact ⟨⟨g, hg⟩, rfl⟩
    calc S.card = Nat.card (S : Set α) := (Nat.card_coe_set_eq _).symm ▸ by simp
      _ ≤ Nat.card (MulAction.orbit K b) := Nat.card_mono (Set.toFinite _) hsub
  · apply le_of_eq
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }

end CFSG.Certificates
