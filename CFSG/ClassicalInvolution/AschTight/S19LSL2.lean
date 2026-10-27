module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def slU (s : F) : SL(2, F) := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def slV (s : F) : SL(2, F) := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_slU (s : F) : ((slU s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, s; 0, 1] := rfl

theorem coe_slV (s : F) : ((slV s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; s, 1] := rfl

open scoped commutatorElement in
theorem neg_one_eq_commutator_of_three (h3 : (3 : F) = 0) :
    ⁅⁅slU (1 : F), slV (1 : F)⁆, ⁅slU (1 : F), slV (-1 : F)⁆⁆ = -1 := by
  apply Subtype.ext
  simp only [commutatorElement_def, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one, coe_slU, coe_slV, Matrix.adjugate_fin_two_of,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination (-2 : F) * h3
  · linear_combination (2 : F) * h3
  · linear_combination (-2 : F) * h3
  · linear_combination (2 : F) * h3

open scoped commutatorElement in
theorem neg_one_mem_derived [Finite F] (h2 : (2 : F) ≠ 0) :
    (-1 : SL(2, F)) ∈ ⁅⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆,
      ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆⁆ := by
  have : Fintype F := Fintype.ofFinite F
  by_cases h4 : 4 ≤ Nat.card F
  · obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    have hP : Group.IsPerfect SL(2, F) :=
      CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl (Or.inr ⟨s, hs⟩)
    have h1 : ⁅(⊤ : Subgroup SL(2, F)), (⊤ : Subgroup SL(2, F))⁆ = ⊤ := hP.commutator_eq_top
    rw [h1, h1]
    exact Subgroup.mem_top _
  · have hF2 : 2 ≤ Nat.card F := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hc : (Nat.card F : F) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero F
    rcases (by omega : Nat.card F = 2 ∨ Nat.card F = 3) with h | h
    · rw [h] at hc
      exact absurd (by exact_mod_cast hc) h2
    · rw [h] at hc
      have h3 : (3 : F) = 0 := by exact_mod_cast hc
      rw [← neg_one_eq_commutator_of_three h3]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
