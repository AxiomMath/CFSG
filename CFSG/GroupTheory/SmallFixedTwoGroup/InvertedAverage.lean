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

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

theorem exists_mem_card_mul_le_card_coset_inter [Finite G] (H : Subgroup G) (S : Set G)
    (hS : S.Nonempty) :
    ∃ x ∈ S, Nat.card H * Nat.card S ≤
      Nat.card G * Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hcard :
      Nat.card (Σ x : G, {y : G // y ∈ S ∧ y * x⁻¹ ∈ H})
        = ∑ x : G, Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    exact Finset.sum_congr rfl fun x _ => (Nat.card_eq_fintype_card).symm
  have hprod :
      Nat.card (Σ x : G, {y : G // y ∈ S ∧ y * x⁻¹ ∈ H})
        = Nat.card H * Nat.card S := by
    have e : (Σ x : G, {y : G // y ∈ S ∧ y * x⁻¹ ∈ H}) ≃ ({y : G // y ∈ S} × H) :=
      (Equiv.subtypeProdEquivSigmaSubtype (fun x y : G => y ∈ S ∧ y * x⁻¹ ∈ H)).symm.trans
        { toFun := fun c => (⟨c.1.2, c.2.1⟩, ⟨c.1.2 * c.1.1⁻¹, c.2.2⟩)
          invFun := fun b =>
            ⟨((b.2 : G)⁻¹ * b.1.1, b.1.1),
              ⟨b.1.2, by
                have h : b.1.1 * ((b.2 : G)⁻¹ * b.1.1)⁻¹ = (b.2 : G) := by group
                rw [h]
                exact b.2.2⟩⟩
          left_inv := by
            rintro ⟨⟨x, y⟩, hyS, hyH⟩
            apply Subtype.ext
            apply Prod.ext <;> group
          right_inv := by
            rintro ⟨⟨y, hyS⟩, ⟨h, hh⟩⟩
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              group }
    rw [Nat.card_congr e, Nat.card_prod]
    exact Nat.mul_comm _ _
  have hsum :
      (∑ x : G, Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H}) = Nat.card H * Nat.card S := by
    rw [← hcard]
    exact hprod
  have hle :
      (∑ _x : G, (Nat.card H * Nat.card S))
        ≤ ∑ x : G, Nat.card G * Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} := by
    have hconst : (∑ _x : G, (Nat.card H * Nat.card S))
        = Nat.card G * (Nat.card H * Nat.card S) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      simp only [Nat.card_eq_fintype_card]
    rw [hconst, ← Finset.mul_sum, hsum]
  obtain ⟨x, -, hxle⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  haveI : Nonempty H := ⟨1⟩
  haveI : Nonempty ↥S := hS.to_subtype
  have hposHS : 0 < Nat.card H * Nat.card S := Nat.mul_pos Nat.card_pos Nat.card_pos
  have hposprod : 0 < Nat.card G * Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} :=
    lt_of_lt_of_le hposHS hxle
  have hfxpos : 0 < Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} := by
    rcases Nat.eq_zero_or_pos (Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H}) with h | h
    · rw [h, mul_zero] at hposprod
      exact absurd hposprod (lt_irrefl 0)
    · exact h
  obtain ⟨⟨y, hyS, hyH⟩⟩ := (Nat.card_pos_iff.mp hfxpos).1
  have hiff : ∀ z : G, (z ∈ S ∧ z * y⁻¹ ∈ H) ↔ (z ∈ S ∧ z * x⁻¹ ∈ H) := by
    intro z
    constructor
    · rintro ⟨hzS, hzH⟩
      refine ⟨hzS, ?_⟩
      have hz' : z * x⁻¹ = (z * y⁻¹) * (y * x⁻¹) := by group
      rw [hz']
      exact H.mul_mem hzH hyH
    · rintro ⟨hzS, hzH⟩
      refine ⟨hzS, ?_⟩
      have hz' : z * y⁻¹ = (z * x⁻¹) * (y * x⁻¹)⁻¹ := by group
      rw [hz']
      exact H.mul_mem hzH (H.inv_mem hyH)
  have hfib : Nat.card {z : G // z ∈ S ∧ z * y⁻¹ ∈ H}
      = Nat.card {z : G // z ∈ S ∧ z * x⁻¹ ∈ H} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  exact ⟨y, hyS, by rw [hfib]; exact hxle⟩

end CFSG.GroupTheory.SmallFixedTwoGroup
