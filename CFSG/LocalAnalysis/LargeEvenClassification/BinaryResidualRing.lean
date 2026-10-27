module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.MinimalAxioms
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

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def BinaryResidualRing := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

@[expose] def binaryResidualAddition (first second : BinaryResidualRing) : BinaryResidualRing :=
  ((first.1.1 + second.1.1, first.1.2 + second.1.2),
    (first.2.1 + second.2.1, first.2.2 + second.2.2))

instance binaryResidualAdd : Add BinaryResidualRing := ⟨binaryResidualAddition⟩

instance binaryResidualZero : Zero BinaryResidualRing := ⟨((0, 0), (0, 0))⟩

instance binaryResidualNeg : Neg BinaryResidualRing :=
  ⟨fun element => ((-element.1.1, -element.1.2), (-element.2.1, -element.2.2))⟩

instance binaryResidualOne : One BinaryResidualRing := ⟨((1, 0), (0, 1))⟩

@[expose] def binaryResidualMultiply (first second : BinaryResidualRing) : BinaryResidualRing :=
  ((first.1.1 * second.1.1, first.1.1 * second.1.2 + first.1.2 * second.2.2),
    (first.2.1 * second.1.1 + first.2.2 * second.2.1, first.2.2 * second.2.2))

instance binaryResidualMul : Mul BinaryResidualRing := ⟨binaryResidualMultiply⟩

instance binaryResidualFintype : Fintype BinaryResidualRing :=
  inferInstanceAs (Fintype ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)))

instance binaryResidualDecidableEq : DecidableEq BinaryResidualRing :=
  inferInstanceAs (DecidableEq ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)))

instance binaryResidualRing : Ring BinaryResidualRing :=
  Ring.ofMinimalAxioms
    (by
      intro first second third
      change binaryResidualAddition (binaryResidualAddition first second) third =
        binaryResidualAddition first (binaryResidualAddition second third)
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualAddition, add_assoc])
    (by
      intro element
      change binaryResidualAddition ((0, 0), (0, 0)) element = element
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualAddition, zero_add])
    (by
      intro element
      let : AddCommGroup (ZMod 2) := (ZMod.commRing 2).toAddCommGroup
      change binaryResidualAddition ((-element.1.1, -element.1.2), (-element.2.1, -element.2.2)) element =
        ((0, 0), (0, 0))
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualAddition, _root_.neg_add_cancel])
    (by
      intro first second third
      change binaryResidualMultiply (binaryResidualMultiply first second) third =
        binaryResidualMultiply first (binaryResidualMultiply second third)
      apply Prod.ext <;> apply Prod.ext <;> simp only [binaryResidualMultiply] <;> ring)
    (by
      intro element
      change binaryResidualMultiply ((1, 0), (0, 1)) element = element
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualMultiply, one_mul, zero_mul, zero_add, add_zero])
    (by
      intro element
      change binaryResidualMultiply element ((1, 0), (0, 1)) = element
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualMultiply, mul_one, mul_zero, zero_add, add_zero])
    (by
      intro first second third
      change binaryResidualMultiply first (binaryResidualAddition second third) =
        binaryResidualAddition (binaryResidualMultiply first second) (binaryResidualMultiply first third)
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualMultiply, binaryResidualAddition] <;> ring)
    (by
      intro first second third
      change binaryResidualMultiply (binaryResidualAddition first second) third =
        binaryResidualAddition (binaryResidualMultiply first third) (binaryResidualMultiply second third)
      apply Prod.ext <;> apply Prod.ext <;>
        simp only [binaryResidualMultiply, binaryResidualAddition] <;> ring)

@[expose] def binaryResidualUnitCandidate (unit : BinaryResidualRingˣ) : ZMod 2 × ZMod 2 :=
  (unit.val.1.2, unit.val.2.1)

theorem binaryResidualUnit_diagonal (unit : BinaryResidualRingˣ) :
    unit.val.1.1 = 1 ∧ unit.val.2.2 = 1 := by
  have hfirst := congrArg (fun entry : BinaryResidualRing => entry.1.1) unit.val_inv
  have hsecond := congrArg (fun entry : BinaryResidualRing => entry.2.2) unit.val_inv
  have hproduct : ∀ first second : ZMod 2, first * second = 1 → first = 1 := by decide
  exact ⟨hproduct _ _ hfirst, hproduct _ _ hsecond⟩

theorem binaryResidualUnitCandidate_injective : Function.Injective binaryResidualUnitCandidate := by
  intro first second heq
  apply Units.ext
  apply Prod.ext <;> apply Prod.ext
  · exact (binaryResidualUnit_diagonal first).1.trans (binaryResidualUnit_diagonal second).1.symm
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq
  · exact (binaryResidualUnit_diagonal first).2.trans (binaryResidualUnit_diagonal second).2.symm

theorem binaryResidualUnit_card_le : Nat.card BinaryResidualRingˣ ≤ 4 := by
  have hbound := Nat.card_le_card_of_injective binaryResidualUnitCandidate binaryResidualUnitCandidate_injective
  have hcard : Nat.card (ZMod 2 × ZMod 2) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact hcard ▸ hbound

end CFSG.LargeEvenClassification.Helpers
