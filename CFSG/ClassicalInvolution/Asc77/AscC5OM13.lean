module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM12

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open Polynomial
open scoped Matrix

variable {F : Type} [Field F]

theorem form_neg_left' (u v : Fin 2 ⊕ Fin 2 → F) : form (-u) v = -form u v := by
  rw [show -u = (-1 : F) • u by simp, form_smul_left]
  ring

theorem form_neg_right' (u v : Fin 2 ⊕ Fin 2 → F) : form u (-v) = -form u v := by
  rw [show -v = (-1 : F) • v by simp, form_smul_right]
  ring

theorem form_self' (u : Fin 2 ⊕ Fin 2 → F) : form u u = 0 := form_self u

theorem form_gm_gm (M : gsp 2 F) (x y : Fin 2 ⊕ Fin 2 → F) :
    form (gm M *ᵥ x) (gm M *ᵥ y) = mu M * form x y := by
  have h := gm_transpose_mul M
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

variable {M : gsp 2 F}

theorem gm_gm_mulVec_of_minus (hN : gm M * gm M = (-mu M) • 1) (x : Fin 2 ⊕ Fin 2 → F) :
    gm M *ᵥ (gm M *ᵥ x) = -(mu M • x) := by
  rw [Matrix.mulVec_mulVec, hN, Matrix.smul_mulVec, Matrix.one_mulVec, neg_smul]

theorem form_gm_left_of_minus (hN : gm M * gm M = (-mu M) • 1) (x y : Fin 2 ⊕ Fin 2 → F) :
    form (gm M *ᵥ x) y = -form x (gm M *ᵥ y) := by
  have hμ : mu M ≠ 0 := Units.ne_zero _
  have h := form_gm_gm M (gm M *ᵥ x) y
  rw [gm_gm_mulVec_of_minus hN, form_neg_left', form_smul_left] at h
  have h' : mu M * (form (gm M *ᵥ x) y + form x (gm M *ᵥ y)) = 0 := by linear_combination -h
  have := (mul_eq_zero.mp h').resolve_left hμ
  linear_combination this

theorem form_gm_symm_of_minus (hN : gm M * gm M = (-mu M) • 1) (x y : Fin 2 ⊕ Fin 2 → F) :
    form y (gm M *ᵥ x) = form x (gm M *ᵥ y) := by
  rw [form_antisymm, form_gm_left_of_minus hN, neg_neg]

theorem exists_form_gm_ne (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = (-mu M) • 1) :
    ∃ x, form x (gm M *ᵥ x) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hz : ∀ x y, form x (gm M *ᵥ y) = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [Matrix.mulVec_add, form_add_left, form_add_right, form_add_right, hcon x, hcon y] at h
    have hs := form_gm_symm_of_minus hN x y
    have : (2 : F) * form x (gm M *ᵥ y) = 0 := by linear_combination h - hs
    exact (mul_eq_zero.1 this).resolve_left h2
  have h0 : ∀ y, gm M *ᵥ y = 0 := fun y => C25W.Sp.eq_zero_of_form_left (m := 1) _ (fun x => hz x y)
  have h3 := gm_gm_mulVec_of_minus hN (Pi.single (Sum.inl 0) 1)
  rw [h0] at h3
  have h4 := congrFun h3 (Sum.inl 0)
  simp at h4

theorem exists_sq_add_mul_sq [Fintype F] (hodd : Fintype.card F % 2 = 1) {μ : F} (hμ : μ ≠ 0)
    (c : F) : ∃ x y : F, x * x + μ * (y * y) = c := by
  have hf : degree (X ^ 2 : F[X]) = 2 := degree_X_pow 2
  have hg : degree (C μ * X ^ 2 - C c : F[X]) = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hμ]; norm_num), degree_C_mul_X_pow 2 hμ]
    rfl
  obtain ⟨x, y, hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  refine ⟨x, y, ?_⟩
  simp only [eval_pow, eval_X, eval_sub, eval_mul, eval_C] at hxy
  linear_combination hxy

theorem form_gm_comb (hN : gm M * gm M = (-mu M) • 1) (x : Fin 2 ⊕ Fin 2 → F) (α β : F) :
    form (α • x + β • (gm M *ᵥ x)) (gm M *ᵥ (α • x + β • (gm M *ᵥ x))) =
      (α * α + mu M * (β * β)) * form x (gm M *ᵥ x) := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, gm_gm_mulVec_of_minus hN]
  simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, form_neg_right',
    form_self']
  rw [form_antisymm (gm M *ᵥ x) x]
  ring

theorem exists_form_gm_eq_one [Finite F] (h2 : (2 : F) ≠ 0) (hN : gm M * gm M = (-mu M) • 1)
    {x : Fin 2 ⊕ Fin 2 → F} (hx : form x (gm M *ᵥ x) ≠ 0) :
    ∃ α β : F, form (α • x + β • (gm M *ᵥ x)) (gm M *ᵥ (α • x + β • (gm M *ᵥ x))) = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hodd : Fintype.card F % 2 = 1 :=
    FiniteField.odd_card_of_char_ne_two (C25W.Sp.ringChar_ne_two_of_two_ne_zero h2)
  obtain ⟨α, β, hαβ⟩ := exists_sq_add_mul_sq hodd (Units.ne_zero (multiplier 2 F M))
    (form x (gm M *ᵥ x))⁻¹
  refine ⟨α, β, ?_⟩
  rw [form_gm_comb hN, hαβ, inv_mul_cancel₀ hx]

end CFSG.ClassicalInvolution.Asc77.C5O.M
