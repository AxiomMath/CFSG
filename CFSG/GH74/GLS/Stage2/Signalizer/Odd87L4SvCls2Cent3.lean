module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls2Cent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Cent3

variable {F : Type} [Field F]

@[expose] def hMat₁ (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, c, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, c⁻¹, 0]

@[expose] def hMat₂ (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; c⁻¹, 0, 0, 0; 0, 0, 0, c; 0, 0, 1, 0]

theorem det_hMat₁ {c : F} (hc : c ≠ 0) : (hMat₁ c).det = 1 := by
  rw [hMat₁, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, hc]

theorem det_hMat₂ {c : F} (hc : c ≠ 0) : (hMat₂ c).det = 1 := by
  rw [hMat₂, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, hc]

theorem hMat₁_comm {c : F} (hc : c ≠ 0) : hMat₁ c * stdN c = stdN c * hMat₁ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat₁, stdN, Matrix.mul_apply, Fin.sum_univ_four, hc]

theorem hMat₂_comm {c : F} (hc : c ≠ 0) : hMat₂ c * stdN c = stdN c * hMat₂ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hMat₂, stdN, Matrix.mul_apply, Fin.sum_univ_four, hc]

theorem hMat₁_uMat {c : F} (hc : c ≠ 0) (a b : F) :
    hMat₁ c * uMat c a b = uMat c (c * a) (c * b) * hMat₁ c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat₁, uMat, Matrix.mul_apply, Fin.sum_univ_four, hc]
  all_goals first | ring1 | field_simp

theorem hMat₂_lMat {c : F} (hc : c ≠ 0) (a b : F) :
    hMat₂ c * lMat c a b = lMat c (c * a) (c * b) * hMat₂ c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hMat₂, lMat, Matrix.mul_apply, Fin.sum_univ_four, hc]
  all_goals first | ring1 | field_simp

@[expose] def hSL₁ (c : Fˣ) : SL(4, F) := ⟨hMat₁ (c : F), det_hMat₁ c.ne_zero⟩

@[expose] def hSL₂ (c : Fˣ) : SL(4, F) := ⟨hMat₂ (c : F), det_hMat₂ c.ne_zero⟩

theorem hSL₁_mem_commSub (c : Fˣ) : hSL₁ c ∈ commSub (c : F) := hMat₁_comm c.ne_zero

theorem hSL₂_mem_commSub (c : Fˣ) : hSL₂ c ∈ commSub (c : F) := hMat₂_comm c.ne_zero

theorem comm_hSL₁_uSL (c : Fˣ) (a b : F) :
    ⁅hSL₁ c, uSL (c : F) a b⁆ = uSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) := by
  have h1 : hSL₁ c * uSL (c : F) a b = uSL (c : F) ((c : F) * a) ((c : F) * b) * hSL₁ c :=
    Subtype.ext (hMat₁_uMat c.ne_zero a b)
  have h2 : uSL (c : F) ((c : F) * a) ((c : F) * b) =
      uSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) * uSL (c : F) a b := by
    rw [uSL_mul]
    congr 1 <;> ring
  rw [commutatorElement_def, h1, h2]
  group

theorem comm_hSL₂_lSL (c : Fˣ) (a b : F) :
    ⁅hSL₂ c, lSL (c : F) a b⁆ = lSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) := by
  have h1 : hSL₂ c * lSL (c : F) a b = lSL (c : F) ((c : F) * a) ((c : F) * b) * hSL₂ c :=
    Subtype.ext (hMat₂_lMat c.ne_zero a b)
  have h2 : lSL (c : F) ((c : F) * a) ((c : F) * b) =
      lSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) * lSL (c : F) a b := by
    rw [lSL_mul]
    congr 1 <;> ring
  rw [commutatorElement_def, h1, h2]
  group

theorem cls2_cent3_frame (c : Fˣ) (hc : ¬ IsSquare (c : F)) (x : SL(4, F))
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub (conjAut 4 F (stdGL c)) →
      proj 4 F b ∈ fixSub (conjAut 4 F (stdGL c)) → x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    conjAut 4 F (stdGL c) (proj 4 F x) = proj 4 F x := by
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hc1 : (c : F) - 1 ≠ 0 := by
    intro h0
    apply hc
    have h1 : (c : F) = 1 := by linear_combination h0
    rw [h1]
    exact ⟨1, (mul_one 1).symm⟩
  have he : ((c : F) - 1) * ((c : F) - 1)⁻¹ = 1 := mul_inv_cancel₀ hc1
  have hu : ∀ a b : F, x * uSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) =
      uSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) * x := fun a b => by
    have := h (hSL₁ c) (uSL (c : F) a b)
      (proj_mem_fixSub_of_mem_commSub c (hSL₁_mem_commSub c))
      (proj_mem_fixSub_of_mem_commSub c (uSL_mem_commSub _ a b))
    rwa [comm_hSL₁_uSL] at this
  have hl : ∀ a b : F, x * lSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) =
      lSL (c : F) (((c : F) - 1) * a) (((c : F) - 1) * b) * x := fun a b => by
    have := h (hSL₂ c) (lSL (c : F) a b)
      (proj_mem_fixSub_of_mem_commSub c (hSL₂_mem_commSub c))
      (proj_mem_fixSub_of_mem_commSub c (lSL_mem_commSub _ a b))
    rwa [comm_hSL₂_lSL] at this
  have e1 : (x : Matrix (Fin 4) (Fin 4) F) * uMat (c : F) 1 0 = uMat (c : F) 1 0 * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (hu ((c : F) - 1)⁻¹ 0)
    rwa [he, mul_zero, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_uSL] at this
  have e2 : (x : Matrix (Fin 4) (Fin 4) F) * lMat (c : F) 1 0 = lMat (c : F) 1 0 * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (hl ((c : F) - 1)⁻¹ 0)
    rwa [he, mul_zero, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_lSL] at this
  have e3 : (x : Matrix (Fin 4) (Fin 4) F) * uMat (c : F) 0 1 = uMat (c : F) 0 1 * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (hu 0 ((c : F) - 1)⁻¹)
    rwa [he, mul_zero, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_uSL] at this
  exact proj_mem_fixSub_of_mem_commSub c (comm_stdN_of_U01 hc0 _ e1 e2 e3)

theorem l4_cls2_cent3 (_hF : Nat.card F = 3) {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F}
    {c : Fˣ} (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) (hc : ¬ IsSquare (c : F))
    (hα : α = conjAut 4 F A) (x : SL(4, F))
    (hx : ∃ r n : ℕ, r.Prime ∧ 5 ≤ r ∧ x ^ (r ^ n) = 1)
    (h : ∀ a b : SL(4, F), proj 4 F a ∈ fixSub α → proj 4 F b ∈ fixSub α →
      x * ⁅a, b⁆ = ⁅a, b⁆ * x) :
    α (proj 4 F x) = proj 4 F x := by
  obtain ⟨P, hP⟩ := exists_normal_form hA hc
  subst hα
  exact cent3_transport_fix P hP (fun x₀ _ h₀ => cls2_cent3_frame c hc x₀ h₀) x hx h

end Cent3

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
