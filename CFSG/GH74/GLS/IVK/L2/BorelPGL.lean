module

public import CFSG.GH74.GLS.IVK.L2.BorelMatrices

public section

namespace CFSG.GH74.GLS.IVK.L2Borel

open CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def borGL (a : Fˣ) (b : F) : GL (Fin 2) F where
  val := !![(a : F), b; 0, 1]
  inv := !![((a⁻¹ : Fˣ) : F), -(((a⁻¹ : Fˣ) : F) * b); 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem borGL_val (a : Fˣ) (b : F) :
    ((borGL a b : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(a : F), b; 0, 1] := rfl

@[expose] def bor (a : Fˣ) (b : F) : PGL(2, F) := Matrix.ProjGenLinGroup.mk (borGL a b)

theorem bor_one (b : F) : bor 1 b = Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip b)) := by
  rw [bor, toPGL_mk_eq]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem bor_mul_unip (a : Fˣ) (b t : F) :
    bor a b * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip ((a : F) * t))) * bor a b := by
  rw [bor, toPGL_mk_eq, toPGL_mk_eq, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

theorem bor_conj_unip (a : Fˣ) (b t : F) :
    bor a b * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) * (bor a b)⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip ((a : F) * t))) := by
  rw [bor_mul_unip, mul_inv_cancel_right]

theorem exists_eq_bor {g : PGL(2, F)} {s : F}
    (hg : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip 1)) * g⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip s))) :
    ∃ (a : Fˣ) (b : F), g = bor a b := by
  rw [mul_inv_eq_iff_eq_mul] at hg
  induction g using Matrix.ProjGenLinGroup.induction_on with
  | mk ĝ =>
  rw [toPGL_mk_eq (unip 1), toPGL_mk_eq (unip s), ← map_mul, ← map_mul,
    Matrix.ProjGenLinGroup.mk_eq_mk_iff] at hg
  obtain ⟨u, hu⟩ := hg
  have e00 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  have e01 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 0 1) hu
  have e10 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 0) hu
  have e11 := congrArg (fun X : GL (Fin 2) F => (X : Matrix (Fin 2) (Fin 2) F) 1 1) hu
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := L2BN.det_ne_zero ĝ
  have hu1 : (u : F) = 1 := by
    by_contra hne
    have hne' : (u : F) - 1 ≠ 0 := sub_ne_zero.2 hne
    have hc : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 * ((u : F) - 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hne'
    have hd : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 * ((u : F) - 1) = 0 := by
        linear_combination e11 - (u : F) * hc
      exact (mul_eq_zero.1 this).resolve_right hne'
    have ha : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
      have : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 * ((u : F) - 1) = 0 := by
        linear_combination e00 + s * hc
      exact (mul_eq_zero.1 this).resolve_right hne'
    apply hdet
    rw [ha, hd, hc]
    ring
  rw [hu1] at e00 e01 e11
  have hc : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e11
  have hd0 : (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    intro h
    apply hdet
    rw [hc, h]
    ring
  have ha0 : (ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h
    apply hdet
    rw [hc, h]
    ring
  refine ⟨Units.mk0 ((ĝ : Matrix (Fin 2) (Fin 2) F) 0 0 / (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1)
    (div_ne_zero ha0 hd0), (ĝ : Matrix (Fin 2) (Fin 2) F) 0 1 / (ĝ : Matrix (Fin 2) (Fin 2) F) 1 1,
    ?_⟩
  rw [bor, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 _ (inv_ne_zero hd0), ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc] <;>
    try field_simp

end CFSG.GH74.GLS.IVK.L2Borel
