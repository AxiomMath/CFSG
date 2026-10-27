module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.Sec312

open QuadraticMap

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem map_add' (a b : V) : Q (a + b) = Q a + Q b + polar Q a b := by
  simp only [polar]
  abel

theorem eq_one_of_aniso {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, Q w = 0 → w = 0) {w : V}
    (hw : w ∈ W) (hw0 : w ≠ 0) : Q w = 1 :=
  (zmod2_eq_zero_or_one _).resolve_left fun h => hw0 (hW w hw h)

theorem polar_eq_one_of_aniso {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, Q w = 0 → w = 0)
    {a b : V} (ha : a ∈ W) (hb : b ∈ W) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    polar Q a b = 1 := by
  have hab0 : a + b ≠ 0 := by
    intro h
    apply hab
    rw [eq_neg_of_add_eq_zero_left h, ZModModule.neg_eq_self]
  have h := map_add' (Q := Q) a b
  rw [eq_one_of_aniso hW (W.add_mem ha hb) hab0, eq_one_of_aniso hW ha ha0,
    eq_one_of_aniso hW hb hb0] at h
  rcases zmod2_eq_zero_or_one (polar Q a b) with h0 | h1
  · rw [h0] at h
    exact absurd h (by decide)
  · exact h1

theorem card_le_four_of_aniso [Finite V] {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, Q w = 0 → w = 0) : Nat.card W ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have hpick : ∀ s : Finset V, s.card ≤ 4 → ∃ c ∈ W, c ∉ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have hsub : (W : Set V) ⊆ (s : Set V) := fun c hc => hcon c hc
    have h1 := Set.ncard_le_ncard hsub (s.finite_toSet)
    rw [Set.ncard_coe_finset] at h1
    have h2 : Nat.card W = (W : Set V).ncard := Nat.card_coe_set_eq (W : Set V)
    omega
  obtain ⟨a, ha, ha0⟩ := hpick {0} (by simp)
  obtain ⟨b, hb, hb0⟩ := hpick {0, a} (Finset.card_le_two.trans (by norm_num))
  obtain ⟨c, hc, hc0⟩ := hpick {0, a, b, a + b} (Finset.card_le_four)
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha0 hb0 hc0
  obtain ⟨hb0, hba⟩ := hb0
  obtain ⟨hc0, hca, hcb, hcab⟩ := hc0
  have habc : a + b + c ≠ 0 := by
    intro h
    apply hcab
    rw [eq_neg_of_add_eq_zero_right h, ZModModule.neg_eq_self]
  have hab := polar_eq_one_of_aniso hW ha hb ha0 hb0 (Ne.symm hba)
  have hac := polar_eq_one_of_aniso hW ha hc ha0 hc0 (Ne.symm hca)
  have hbc := polar_eq_one_of_aniso hW hb hc hb0 hc0 (Ne.symm hcb)
  have h0 : Q (a + b + c) = 0 := by
    rw [map_add' (a + b) c, map_add' a b, polar_add_left, eq_one_of_aniso hW ha ha0,
      eq_one_of_aniso hW hb hb0, eq_one_of_aniso hW hc hc0, hab, hac, hbc]
    decide
  exact habc (hW _ (W.add_mem (W.add_mem ha hb) hc) h0)

theorem map_sub_add_polar_eq_zero {t : V ≃ₗ[ZMod 2] V} (ht : ∀ v, Q (t v) = Q v) (v : V) :
    Q (t v - v) + polar Q v (t v - v) = 0 := by
  have h := map_add' (Q := Q) v (t v - v)
  rw [add_sub_cancel, ht] at h
  have h2 : Q v + (Q (t v - v) + polar Q v (t v - v)) = Q v + 0 := by
    rw [add_zero, ← add_assoc]
    exact h.symm
  exact add_left_cancel h2

theorem polar_sub_eq_zero_of_fixed {t : V ≃ₗ[ZMod 2] V} (ht : ∀ v, Q (t v) = Q v) {x : V}
    (hx : t x = x) (v : V) : polar Q x (t v - v) = 0 := by
  have h1 := map_sub_add_polar_eq_zero ht (v + x)
  have h2 := map_sub_add_polar_eq_zero ht v
  have e : t (v + x) - (v + x) = t v - v := by
    rw [map_add, hx]
    abel
  rw [e, polar_add_left, ← add_assoc, h2, zero_add] at h1
  exact h1

theorem card_le_two_of_aniso [Finite V] {W : Submodule (ZMod 2) V}
    (hW : ∀ w ∈ W, Q w = 0 → w = 0) (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hiso : ∀ t ∈ H, ∀ v, Q (t v) = Q v) (hrange : ∀ t ∈ H, ∀ v, t v - v ∈ W)
    (hfix : ∀ t ∈ H, ∀ w ∈ W, t w = w) : Nat.card H ≤ 2 := by
  classical
  have hval : ∀ t ∈ H, ∀ v w, t v - v ≠ 0 → t w - w ≠ 0 → t v - v = t w - w := by
    intro t ht v w hv hw
    by_contra hne
    have h1 := polar_sub_eq_zero_of_fixed (hiso t ht) (hfix t ht _ (hrange t ht v)) w
    rw [polar_eq_one_of_aniso hW (hrange t ht v) (hrange t ht w) hv hw hne] at h1
    exact one_ne_zero h1
  have hkey : ∀ t ∈ H, ∀ u, t u - u ≠ 0 → ∀ v, (t v - v ≠ 0 ↔ polar Q v (t u - u) = 1) := by
    intro t ht u hu v
    constructor
    · intro hv
      have h := map_sub_add_polar_eq_zero (hiso t ht) v
      rw [hval t ht v u hv hu, eq_one_of_aniso hW (hrange t ht u) hu] at h
      rcases zmod2_eq_zero_or_one (polar Q v (t u - u)) with h0 | h1
      · rw [h0] at h
        exact absurd h (by decide)
      · exact h1
    · intro h hv
      have hv' : t v = v := sub_eq_zero.mp hv
      rw [polar_sub_eq_zero_of_fixed (hiso t ht) hv' u] at h
      exact zero_ne_one h
  have hne1 : ∀ t ∈ H, t ≠ 1 → ∃ u, t u - u ≠ 0 := by
    intro t ht h1
    by_contra hcon
    push Not at hcon
    exact h1 (LinearEquiv.ext fun v => by simpa [sub_eq_zero] using hcon v)
  have hdet : ∀ t₁ ∈ H, ∀ t₂ ∈ H, t₁ ≠ 1 → t₂ ≠ 1 → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ h₁1 h₂1
    obtain ⟨u₁, hu₁⟩ := hne1 t₁ h₁ h₁1
    obtain ⟨u₂, hu₂⟩ := hne1 t₂ h₂ h₂1
    have hc : t₁ u₁ - u₁ = t₂ u₂ - u₂ := by
      by_contra hne
      have h1 := polar_sub_eq_zero_of_fixed (hiso t₂ h₂) (hfix t₂ h₂ _ (hrange t₁ h₁ u₁)) u₂
      rw [polar_eq_one_of_aniso hW (hrange t₁ h₁ u₁) (hrange t₂ h₂ u₂) hu₁ hu₂ hne] at h1
      exact one_ne_zero h1
    refine LinearEquiv.ext fun v => ?_
    have e : t₁ v - v = t₂ v - v := by
      by_cases hv : t₁ v - v = 0
      · have hv2 : ¬ t₂ v - v ≠ 0 := by
          rw [hkey t₂ h₂ u₂ hu₂ v, ← hc, ← hkey t₁ h₁ u₁ hu₁ v]
          exact not_not.mpr hv
        rw [hv, not_not.mp hv2]
      · have hv2 : t₂ v - v ≠ 0 := by
          rw [hkey t₂ h₂ u₂ hu₂ v, ← hc, ← hkey t₁ h₁ u₁ hu₁ v]
          exact hv
        rw [hval t₁ h₁ v u₁ hv hu₁, hval t₂ h₂ v u₂ hv2 hu₂, hc]
    simpa using e
  by_cases hex : ∃ t ∈ H, t ≠ 1
  · obtain ⟨t₀, ht₀, ht₀1⟩ := hex
    have hsub : (H : Set (V ≃ₗ[ZMod 2] V)) ⊆ {1, t₀} := by
      intro t ht
      by_cases h1 : t = 1
      · exact Or.inl h1
      · exact Or.inr (hdet t ht t₀ ht₀ h1 ht₀1)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_insert_le (1 : V ≃ₗ[ZMod 2] V) {t₀}
    rw [Set.ncard_singleton] at h2
    have h3 : Nat.card H = (H : Set (V ≃ₗ[ZMod 2] V)).ncard := Nat.card_coe_set_eq _
    omega
  · push Not at hex
    have hbot : H = ⊥ := eq_bot_iff.mpr fun t ht => (Subgroup.mem_bot).mpr (hex t ht)
    rw [hbot, Subgroup.card_bot]
    norm_num

end CFSG.ComponentClassification.AS81.Sec312
