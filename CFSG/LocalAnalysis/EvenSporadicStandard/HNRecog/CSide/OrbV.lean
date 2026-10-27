module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

theorem cSide_orbit_invariant {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (q : QuadraticForm (ZMod 2) V) (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V)) (O : Fin 2 → Set V)
    (hcover : ∀ v, (v ≠ 0 ∧ q v = 0) ↔ ∃ i, v ∈ O i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (O i) (O j))
    (hinv : ∀ i g, ∀ v ∈ O i, σ g v ∈ O i)
    (htrans : ∀ i, ∀ v ∈ O i, ∀ w ∈ O i, ∃ g, σ g v = w)
    (h0 : Nat.card (O 0) = 75) (h1 : Nat.card (O 1) = 60)
    (f : V ≃ₗ[ZMod 2] V) (hq : ∀ v, q (f v) = q v)
    (hf : ∀ g, ∃ g', f * σ g * f⁻¹ = σ g') : ∀ i, ∀ v ∈ O i, f v ∈ O i := by
  classical
  have h0n : (O 0).ncard = 75 := h0
  have h1n : (O 1).ncard = 60 := h1
  have hO0 : (O 0).Nonempty := by
    have hpos : 0 < Nat.card (O 0) := by
      rw [h0]
      norm_num
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
  have hO1 : (O 1).Nonempty := by
    have hpos : 0 < Nat.card (O 1) := by
      rw [h1]
      norm_num
    exact Set.nonempty_coe_sort.mp (Nat.card_pos_iff.mp hpos).1
  have hmap_orbit : ∀ i : Fin 2, ∃ j : Fin 2, f '' O i ⊆ O j := by
    intro i
    have hne : (O i).Nonempty := by
      fin_cases i
      · exact hO0
      · exact hO1
    obtain ⟨v0, hv0⟩ := hne
    have hv0q : v0 ≠ 0 ∧ q v0 = 0 := (hcover v0).mpr ⟨i, hv0⟩
    have hfv0 : f v0 ≠ 0 ∧ q (f v0) = 0 := by
      refine ⟨?_, ?_⟩
      · intro hzero
        have : v0 = 0 := by
          have h := congrArg f.symm hzero
          simpa using h
        exact hv0q.1 this
      · rw [hq v0, hv0q.2]
    obtain ⟨j, hj⟩ := (hcover (f v0)).mp hfv0
    refine ⟨j, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨g, hg⟩ := htrans i v0 hv0 w hw
    obtain ⟨g', hg'⟩ := hf g
    have hg'' : f * σ g * f.symm = σ g' := by
      rw [show f⁻¹ = f.symm from rfl] at hg'
      exact hg'
    have hcomp : f (σ g v0) = σ g' (f v0) := by
      have h := congrArg (fun e : V ≃ₗ[ZMod 2] V => e (f v0)) hg''
      simpa only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply] using h
    rw [← hg, hcomp]
    exact hinv j g' (f v0) hj
  have hcard_le : ∀ (i j : Fin 2), f '' O i ⊆ O j → Nat.card (O i) ≤ Nat.card (O j) := by
    intro i j hsub
    calc
      Nat.card (O i) = Nat.card (f '' O i) :=
        (Nat.card_image_of_injective f.injective (O i)).symm
      _ ≤ Nat.card (O j) :=
        Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
  have h0_sub : f '' O 0 ⊆ O 0 := by
    obtain ⟨j, hj⟩ := hmap_orbit 0
    have hj0 : j = 0 := by
      fin_cases j
      · rfl
      · exfalso
        have hle := hcard_le 0 1 hj
        have hlt : (75 : ℕ) ≤ 60 := by
          calc
            (75 : ℕ) = Nat.card (O 0) := h0.symm
            _ ≤ Nat.card (O 1) := hle
            _ = 60 := h1
        norm_num at hlt
    simpa [hj0] using hj
  have h1_sub : f '' O 1 ⊆ O 1 := by
    obtain ⟨k, hk⟩ := hmap_orbit 1
    have hk1 : k = 1 := by
      fin_cases k
      · exfalso
        let U : Set V := O 0 ∪ O 1
        have hunion : f '' U ⊆ O 0 := by
          rintro y ⟨x, hx, rfl⟩
          dsimp [U] at hx
          rcases hx with hx | hx
          · exact h0_sub ⟨x, hx, rfl⟩
          · exact hk ⟨x, hx, rfl⟩
        have hle : Nat.card U ≤ Nat.card (O 0) := by
          calc
            Nat.card U = Nat.card (f '' U) :=
              (Nat.card_image_of_injective f.injective U).symm
            _ ≤ Nat.card (O 0) :=
              Nat.card_le_card_of_injective (Set.inclusion hunion)
                (Set.inclusion_injective hunion)
        have hdisj01 : Disjoint (O 0) (O 1) := hdisj 0 1 (by decide)
        have hcard_union : Nat.card U = 135 := by
          change U.ncard = 135
          dsimp [U]
          rw [Set.ncard_union_eq hdisj01, h0n, h1n]
        have hlt : (135 : ℕ) ≤ 75 := by
          calc
            (135 : ℕ) = Nat.card U := hcard_union.symm
            _ ≤ Nat.card (O 0) := hle
            _ = 75 := h0
        norm_num at hlt
      · rfl
    simpa [hk1] using hk
  intro i v hv
  fin_cases i
  · exact h0_sub ⟨v, hv, rfl⟩
  · exact h1_sub ⟨v, hv, rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
