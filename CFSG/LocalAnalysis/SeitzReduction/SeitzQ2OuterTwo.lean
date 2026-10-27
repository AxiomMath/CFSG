module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Generic

theorem finite_outer_and_card_le_two_of_forall {C : Type*} [Group C] (β : Bool → MulAut C)
    (h : ∀ α : MulAut C, ∃ b, α * (β b)⁻¹ ∈ inner C) :
    Finite (Outer C) ∧ Nat.card (Outer C) ≤ 2 := by
  let f : Bool → Outer C := fun b => (β b : Outer C)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, hb⟩ := h α
    refine ⟨b, ?_⟩
    change ((β b : MulAut C) : Outer C) = (α : Outer C)
    rw [QuotientGroup.eq_iff_div_mem, ← inv_mem_iff, div_eq_mul_inv, mul_inv_rev, inv_inv]
    exact hb
  refine ⟨Finite.of_surjective f hf, ?_⟩
  calc Nat.card (Outer C) ≤ Nat.card Bool := Nat.card_le_card_of_surjective f hf
    _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]

theorem isPGroup_two_of_card_le_two {X : Type*} [Group X] [Finite X] (h : Nat.card X ≤ 2) :
    IsPGroup 2 X := by
  have h1 : 0 < Nat.card X := Nat.card_pos
  rcases (show Nat.card X = 1 ∨ Nat.card X = 2 by omega) with h1 | h2
  · exact IsPGroup.of_card (n := 0) (by rw [h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [h2, pow_one])

theorem finite_outer_and_card_le_two_of_mulEquiv {L C : Type*} [Group L] [Group C] (e : L ≃* C)
    (h : Finite (Outer C) ∧ Nat.card (Outer C) ≤ 2) :
    Finite (Outer L) ∧ Nat.card (Outer L) ≤ 2 := by
  obtain ⟨hfin, hcard⟩ := h
  refine ⟨Finite.of_equiv _ (equivalence e).symm.toEquiv, ?_⟩
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact hcard

end Generic

section FieldTwo

variable {K : Type*} [Field K]

private theorem eq_zero_or_eq_one_of_card_eq_two' (hK : Nat.card K = 2) (c : K) :
    c = 0 ∨ c = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  have h' : c * (c - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.1 h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1)

theorem units_eq_one_of_natCard_eq_two (hK : Nat.card K = 2) (u : Kˣ) : u = 1 := by
  rcases eq_zero_or_eq_one_of_card_eq_two' hK (u : K) with h | h
  · exact absurd h u.ne_zero
  · exact Units.ext h

theorem ringEquiv_eq_refl_of_card_eq_two (hK : Nat.card K = 2) (σ : K ≃+* K) :
    σ = RingEquiv.refl K := by
  ext c
  rcases eq_zero_or_eq_one_of_card_eq_two' hK c with rfl | rfl
  · simp
  · simp

end FieldTwo

section Linear

variable {n : ℕ} {K : Type*} [Field K]

theorem conj_proj_eq_conjAut_toGL (g : Matrix.SpecialLinearGroup (Fin n) K) :
    MulAut.conj (proj n K g) = conjAut n K (Matrix.SpecialLinearGroup.toGL g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n K x
  rw [MulAut.conj_apply, conjAut_proj, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

theorem conjAut_mem_inner_of_card_eq_two (hK : Nat.card K = 2)
    (A : Matrix.GeneralLinearGroup (Fin n) K) : conjAut n K A ∈ inner (projectiveSL n K) := by
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h := units_eq_one_of_natCard_eq_two hK (Matrix.GeneralLinearGroup.det A)
    have h' := congrArg Units.val h
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h'
  set g : Matrix.SpecialLinearGroup (Fin n) K := ⟨A, hdet⟩ with hg
  have hgA : Matrix.SpecialLinearGroup.toGL g = A := Units.ext rfl
  refine ⟨proj n K g, ?_⟩
  rw [conj_proj_eq_conjAut_toGL, hgA]

theorem fieldAut_eq_one_of_card_eq_two (hK : Nat.card K = 2) (σ : K ≃+* K) :
    fieldAut n K σ = 1 := by
  rw [ringEquiv_eq_refl_of_card_eq_two hK σ]
  exact map_one (fieldAut n K)

theorem card_outer_projectiveSL_le_two [Finite K] (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    Finite (Outer (projectiveSL n K)) ∧ Nat.card (Outer (projectiveSL n K)) ≤ 2 := by
  refine finite_outer_and_card_le_two_of_forall (fun b => if b then dualAut n K else 1)
    fun α => ?_
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (K := K) hn).2 α
  rw [fieldAut_eq_one_of_card_eq_two hK σ, mul_one] at hα
  rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
  · refine ⟨false, ?_⟩
    show α * (1 : MulAut (projectiveSL n K))⁻¹ ∈ inner (projectiveSL n K)
    rw [hα, pow_zero, mul_one, inv_one, mul_one]
    exact conjAut_mem_inner_of_card_eq_two hK A
  · refine ⟨true, ?_⟩
    show α * (dualAut n K)⁻¹ ∈ inner (projectiveSL n K)
    rw [hα, pow_one, mul_inv_cancel_right]
    exact conjAut_mem_inner_of_card_eq_two hK A

theorem card_outer_le_two_of_mulEquiv_PSL_two {L : Type*} [Group L] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) :
    Finite (Outer L) ∧ Nat.card (Outer L) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  exact finite_outer_and_card_le_two_of_mulEquiv e (card_outer_projectiveSL_le_two hn hK)

theorem isPGroup_outer_of_mulEquiv_PSL_two {L : Type*} [Group L] (hn : 3 ≤ n)
    (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) : IsPGroup 2 (Outer L) := by
  obtain ⟨hfin, hcard⟩ := card_outer_le_two_of_mulEquiv_PSL_two hn hK e
  exact isPGroup_two_of_card_le_two hcard

end Linear

end CFSG.SeitzReduction.SeitzQ2
