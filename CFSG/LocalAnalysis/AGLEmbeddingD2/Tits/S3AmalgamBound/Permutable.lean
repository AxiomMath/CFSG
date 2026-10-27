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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open scoped Pointwise

theorem coe_sup_eq_mul_of_permutable {G : Type*} [Group G] {Y R : Subgroup G}
    (hc : (Y : Set G) * (R : Set G) = (R : Set G) * (Y : Set G)) :
    ((Y ⊔ R : Subgroup G) : Set G) = (Y : Set G) * (R : Set G) := by
  apply Set.Subset.antisymm
  · let S : Subgroup G :=
      { carrier := (Y : Set G) * (R : Set G)
        one_mem' := ⟨1, Y.one_mem, 1, R.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨y, hy, r, hr, rfl⟩ ⟨y', hy', r', hr', rfl⟩
          have h1 : r * y' ∈ (R : Set G) * (Y : Set G) := ⟨r, hr, y', hy', rfl⟩
          rw [← hc] at h1
          obtain ⟨y'', hy'', r'', hr'', h2⟩ := h1
          have h2 : y'' * r'' = r * y' := h2
          refine ⟨y * y'', Y.mul_mem hy hy'', r'' * r', R.mul_mem hr'' hr', ?_⟩
          calc y * y'' * (r'' * r') = y * (y'' * r'') * r' := by group
            _ = y * (r * y') * r' := by rw [h2]
            _ = y * r * (y' * r') := by group
        inv_mem' := by
          rintro _ ⟨y, hy, r, hr, rfl⟩
          have h1 : r⁻¹ * y⁻¹ ∈ (R : Set G) * (Y : Set G) :=
            ⟨r⁻¹, R.inv_mem hr, y⁻¹, Y.inv_mem hy, rfl⟩
          rw [← hc] at h1
          obtain ⟨y'', hy'', r'', hr'', h2⟩ := h1
          have h2' : y'' * r'' = r⁻¹ * y⁻¹ := h2
          exact ⟨y'', hy'', r'', hr'', by show y'' * r'' = (y * r)⁻¹; rw [h2']; group⟩ }
    have hY : Y ≤ S := fun y hy => ⟨y, hy, 1, R.one_mem, by simp⟩
    have hR : R ≤ S := fun r hr => ⟨1, Y.one_mem, r, hr, by simp⟩
    exact fun x hx => (sup_le hY hR) hx
  · rintro _ ⟨y, hy, r, hr, rfl⟩
    exact Subgroup.mul_mem_sup hy hr

theorem card_sup_of_permutable {G : Type*} [Group G] [Finite G] {Y R : Subgroup G}
    (hc : (Y : Set G) * (R : Set G) = (R : Set G) * (Y : Set G)) (hd : Y ⊓ R = ⊥) :
    Nat.card ↥(Y ⊔ R) = Nat.card ↥Y * Nat.card ↥R := by
  have hcoe := coe_sup_eq_mul_of_permutable hc
  have hY : Y ≤ Y ⊔ R := le_sup_left
  have hR : R ≤ Y ⊔ R := le_sup_right
  have hdisj : Disjoint (Y.subgroupOf (Y ⊔ R)) (R.subgroupOf (Y ⊔ R)) := by
    rw [Subgroup.disjoint_def]
    intro x hxY hxR
    have : (x : G) ∈ Y ⊓ R := ⟨hxY, hxR⟩
    rw [hd, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hmul : ((Y.subgroupOf (Y ⊔ R) : Subgroup ↥(Y ⊔ R)) : Set ↥(Y ⊔ R)) *
      ((R.subgroupOf (Y ⊔ R) : Subgroup ↥(Y ⊔ R)) : Set ↥(Y ⊔ R)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    have hs : (s : G) ∈ ((Y ⊔ R : Subgroup G) : Set G) := s.2
    rw [hcoe] at hs
    obtain ⟨y, hy, r, hr, hyr⟩ := hs
    refine ⟨⟨y, hY hy⟩, ?_, ⟨r, hR hr⟩, ?_, Subtype.ext hyr⟩
    · exact hy
    · exact hr
  have hcomp := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
  have h1 := hcomp.card_mul_card
  have e1 : Nat.card (Y.subgroupOf (Y ⊔ R)) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have e2 : Nat.card (R.subgroupOf (Y ⊔ R)) = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  rw [e1, e2] at h1
  exact h1.symm

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
