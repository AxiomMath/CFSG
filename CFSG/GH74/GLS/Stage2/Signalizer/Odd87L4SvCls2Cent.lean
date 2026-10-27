module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvCls2Frame
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L4SvConj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLb

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatFactsL4U4.InvClassL
open scoped MatrixGroups commutatorElement

section Cent

variable {F : Type} [Field F]

@[expose] def elemU : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def elemL : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem kronSL_elemU (c : F) : kronSL (elemU : SL(2, F)) = uSL c 1 0 :=
  Subtype.ext (by
    rw [coe_kronSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kronM, uSL, uMat, elemU])

theorem kronSL_elemL (c : F) : kronSL (elemL : SL(2, F)) = lSL c 1 0 :=
  Subtype.ext (by
    rw [coe_kronSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kronM, lSL, lMat, elemL])

@[expose] def mMat (c : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, c, -c, 0; 1, 1, 0, -c; 1, 0, 1, -c; 0, 1, -1, 1]

theorem mMat_eq (c : F) : uMat c 0 1 * lMat c 1 0 * uMat c 0 (-1) = mMat c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, lMat, mMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem blk_of_comm (c : F) (x : Matrix (Fin 4) (Fin 4) F) (h1 : x * uMat c 1 0 = uMat c 1 0 * x)
    (h2 : x * lMat c 1 0 = lMat c 1 0 * x) :
    x 0 2 = 0 ∧ x 0 3 = 0 ∧ x 1 2 = 0 ∧ x 1 3 = 0 ∧ x 2 0 = 0 ∧ x 2 1 = 0 ∧ x 3 0 = 0 ∧
      x 3 1 = 0 ∧ x 2 2 = x 0 0 ∧ x 2 3 = x 0 1 ∧ x 3 2 = x 1 0 ∧ x 3 3 = x 1 1 := by
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e02 := congrFun (congrFun h1 0) 2
  have e03 := congrFun (congrFun h1 0) 3
  have e10 := congrFun (congrFun h1 1) 0
  have e11 := congrFun (congrFun h1 1) 1
  have e12 := congrFun (congrFun h1 1) 2
  have e13 := congrFun (congrFun h1 1) 3
  have f00 := congrFun (congrFun h2 0) 0
  have f01 := congrFun (congrFun h2 0) 1
  have f10 := congrFun (congrFun h2 1) 0
  have f11 := congrFun (congrFun h2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e00 e01 e02 e03 e10 e11 e12 e13
  simp [Matrix.mul_apply, Fin.sum_univ_four, lMat] at f00 f01 f10 f11
  exact ⟨f00, f01, f10, f11, e00, e01, e10, e11, by linear_combination -e02,
    by linear_combination -e03, by linear_combination -e12, by linear_combination -e13⟩

theorem comm_stdN_of_rel {c : F} (x : Matrix (Fin 4) (Fin 4) F) (hx02 : x 0 2 = 0)
    (hx03 : x 0 3 = 0) (hx12 : x 1 2 = 0) (hx13 : x 1 3 = 0) (hx20 : x 2 0 = 0)
    (hx21 : x 2 1 = 0) (hx30 : x 3 0 = 0) (hx31 : x 3 1 = 0) (hx22 : x 2 2 = x 0 0)
    (hx23 : x 2 3 = x 0 1) (hx32 : x 3 2 = x 1 0) (hx33 : x 3 3 = x 1 1)
    (hP1 : x 0 1 = c * x 1 0) (hP2 : x 0 0 = x 1 1) : x * stdN c = stdN c * x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stdN, Matrix.mul_apply, Fin.sum_univ_four, hx02, hx03, hx12, hx13, hx20, hx21, hx30,
      hx31, hx22, hx23, hx32, hx33, hP1, hP2]
  all_goals ring

theorem comm_stdN_of_U01 {c : F} (hc : c ≠ 0) (x : Matrix (Fin 4) (Fin 4) F)
    (h1 : x * uMat c 1 0 = uMat c 1 0 * x) (h2 : x * lMat c 1 0 = lMat c 1 0 * x)
    (h3 : x * uMat c 0 1 = uMat c 0 1 * x) : x * stdN c = stdN c * x := by
  obtain ⟨hx02, hx03, hx12, hx13, hx20, hx21, hx30, hx31, hx22, hx23, hx32, hx33⟩ :=
    blk_of_comm c x h1 h2
  have e02 := congrFun (congrFun h3 0) 2
  have e03 := congrFun (congrFun h3 0) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat] at e02 e03
  have hP1 : x 0 1 = c * x 1 0 := by linear_combination e02 + c * hx32
  have hP2 : x 0 0 = x 1 1 := by
    have : c * (x 0 0 - x 1 1) = 0 := by linear_combination e03 + c * hx33
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc
    · exact sub_eq_zero.1 h
  exact comm_stdN_of_rel x hx02 hx03 hx12 hx13 hx20 hx21 hx30 hx31 hx22 hx23 hx32 hx33 hP1 hP2

theorem comm_stdN_of_M {c : F} (hc : c ≠ 0) (x : Matrix (Fin 4) (Fin 4) F)
    (h1 : x * uMat c 1 0 = uMat c 1 0 * x) (h2 : x * lMat c 1 0 = lMat c 1 0 * x)
    (h : x * mMat c = mMat c * x) : x * stdN c = stdN c * x := by
  obtain ⟨hx02, hx03, hx12, hx13, hx20, hx21, hx30, hx31, hx22, hx23, hx32, hx33⟩ :=
    blk_of_comm c x h1 h2
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, mMat] at e00 e01
  have hP1 : x 0 1 = c * x 1 0 := by linear_combination e00 - hx02 - c * hx20
  have hP2 : x 0 0 = x 1 1 := by
    have : c * (x 0 0 - x 1 1) = 0 := by linear_combination e01 - hx03 - c * hx21
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc
    · exact sub_eq_zero.1 h
  exact comm_stdN_of_rel x hx02 hx03 hx12 hx13 hx20 hx21 hx30 hx31 hx22 hx23 hx32 hx33 hP1 hP2

theorem cls2_cent_frame (c : Fˣ) (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub (conjAut 4 F (stdGL c))) →
      ∀ g, x * ι g = ι g * x) :
    conjAut 4 F (stdGL c) (proj 4 F x) = proj 4 F x := by
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hk : ∀ g : SL(2, F), kronSL g ∈ commSub (c : F) := fun g => kronSL_comm g (c : F)
  have h1 := h kronSL (fun g => proj_mem_fixSub_of_mem_commSub c (hk g))
  let ι₂ : SL(2, F) →* SL(4, F) := (MulAut.conj (uSL (c : F) 0 1)).toMonoidHom.comp kronSL
  have hι₂ : ∀ g, ι₂ g ∈ commSub (c : F) := fun g =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (uSL_mem_commSub _ 0 1) (hk g))
      (Subgroup.inv_mem _ (uSL_mem_commSub _ 0 1))
  have h2 := h ι₂ (fun g => proj_mem_fixSub_of_mem_commSub c (hι₂ g))
  have e1 : (x : Matrix (Fin 4) (Fin 4) F) * uMat (c : F) 1 0 = uMat (c : F) 1 0 * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (h1 elemU)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, kronSL_elemU,
      coe_uSL] at this
  have e2 : (x : Matrix (Fin 4) (Fin 4) F) * lMat (c : F) 1 0 = lMat (c : F) 1 0 * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (h1 elemL)
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, kronSL_elemL,
      coe_lSL] at this
  have hι : ι₂ elemL = uSL (c : F) 0 1 * lSL (c : F) 1 0 * uSL (c : F) 0 (-1) := by
    show uSL (c : F) 0 1 * kronSL elemL * (uSL (c : F) 0 1)⁻¹ = _
    rw [kronSL_elemL, uSL_inv, neg_zero]
  have e3 : (x : Matrix (Fin 4) (Fin 4) F) * mMat (c : F) = mMat (c : F) * x := by
    have := congrArg (fun g : SL(4, F) => (g : Matrix (Fin 4) (Fin 4) F)) (h2 elemL)
    rw [hι] at this
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_lSL, mMat_eq] at this
    exact this
  exact proj_mem_fixSub_of_mem_commSub c (comm_stdN_of_M hc0 _ e1 e2 e3)

theorem l4_cls2_cent (_hodd : Odd (Nat.card F)) (_h5 : 5 ≤ Nat.card F)
    {α : MulAut (projectiveSL 4 F)} {A : GL (Fin 4) F} {c : Fˣ}
    (hA : A * A = GeneralLinearGroup.scalar (Fin 4) c) (hc : ¬ IsSquare (c : F))
    (hα : α = conjAut 4 F A) (x : SL(4, F))
    (h : ∀ ι : SL(2, F) →* SL(4, F), (∀ g, proj 4 F (ι g) ∈ fixSub α) →
      ∀ g, x * ι g = ι g * x) :
    α (proj 4 F x) = proj 4 F x := by
  obtain ⟨P, hP⟩ := exists_normal_form hA hc
  subst hα
  exact cent_transport_fix P hP (fun x₀ h₀ => cls2_cent_frame c x₀ h₀) x h

end Cent

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
