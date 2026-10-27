module

public import CFSG.ClassicalInvolution.Asc77.AscCX4L1

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def gMatM (m n : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 1, 0; 0, 2⁻¹, 0, m * 2⁻¹ / n; -1, 0, 1, 0; 0, -(n * 2⁻¹ / m), 0, 2⁻¹]

@[expose] noncomputable def wMat (m n : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, m / n; 1, 0, 0, 0; 0, n / m, 0, 0]

theorem det_gMatM (h2 : (2 : F) ≠ 0) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    (gMatM m n).det = 1 := by
  simp [gMatM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  ring

@[expose] noncomputable def gMat (h2 : (2 : F) ≠ 0) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    SL(4, F) :=
  ⟨gMatM m n, det_gMatM h2 hm hn⟩

theorem gMatM_symp (h2 : (2 : F) ≠ 0) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    gMatM m n * !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] * (gMatM m n)ᵀ =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gMatM, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;>
    field_simp <;> ring

theorem gMatM_mul_z (h2 : (2 : F) ≠ 0) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    gMatM m n * !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = wMat m n * gMatM m n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gMatM, wMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

theorem z_mul_w_sq {m n : F} (hm : m ≠ 0) (hn : n ≠ 0) :
    !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * wMat m n *
      (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * wMat m n) =
        (!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] : Matrix (Fin 4) (Fin 4) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

theorem conj_inv_transpose_of_symp (A : GL (Fin 4) F) (g : SL(4, F))
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      ((g⁻¹).transpose) = g := by
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  have hGi : ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hAi : (A : Matrix (Fin 4) (Fin 4) F) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (A : Matrix (Fin 4) (Fin 4) F) * (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ =
      (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) := by
    calc (A : Matrix (Fin 4) (Fin 4) F) * (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ
        = ((g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
            (g : Matrix (Fin 4) (Fin 4) F)ᵀ) *
              (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ := by rw [hg]
      _ = (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
            ((g : Matrix (Fin 4) (Fin 4) F)ᵀ *
              (((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) := by
          rw [← Matrix.transpose_mul, hGi, Matrix.transpose_one, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc, hAi, Matrix.mul_one]

theorem graph_witness (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F) {m n : F} (hm : m ≠ 0) (hn : n ≠ 0)
    (hA : (A : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :
    ∃ x : projectiveSL 4 F, (conjAut 4 F A * dualAut 4 F) x = x ∧ x * zbar * x⁻¹ ≠ zbar ∧
      x * zbar * x⁻¹ * zbar = zbar * (x * zbar * x⁻¹) := by
  obtain ⟨g, hgdef⟩ : ∃ g : SL(4, F), g = gMat h2 hm hn := ⟨_, rfl⟩
  have hgM : (g : Matrix (Fin 4) (Fin 4) F) = gMatM m n := by rw [hgdef]; rfl
  obtain ⟨r, hrdef⟩ : ∃ r : SL(4, F), r = rootInv F (show 2 ≤ 4 by norm_num) := ⟨_, rfl⟩
  have hz : (r : Matrix (Fin 4) (Fin 4) F) =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
    rw [hrdef, coe_rootInv, negBlock_four]
  have hz2 : r * r = 1 := by
    rw [hrdef, rootInv, ← map_mul, neg_one_mul, neg_neg, map_one]
  obtain ⟨w, hwdef⟩ : ∃ w : SL(4, F), w = g * r * g⁻¹ := ⟨_, rfl⟩
  have hGGi : (g : Matrix (Fin 4) (Fin 4) F) *
      ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hsymp : (g : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F) := by
    rw [hgM, hA]
    exact gMatM_symp h2 hm hn
  have hw : (w : Matrix (Fin 4) (Fin 4) F) = wMat m n := by
    rw [hwdef, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hz, hgM,
      gMatM_mul_z h2 hm hn, ← hgM, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  have hw2 : w * w = 1 := by
    rw [hwdef]
    calc g * r * g⁻¹ * (g * r * g⁻¹) = g * (r * r) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hzb : (zbar : projectiveSL 4 F) = proj 4 F r := by rw [hrdef]
  have hmul : proj 4 F g * zbar * (proj 4 F g)⁻¹ = proj 4 F w := by
    rw [hzb, hwdef, map_mul, map_mul, map_inv]
  refine ⟨proj 4 F g, ?_, ?_, ?_⟩
  · show conjAut 4 F A (dualAut 4 F (proj 4 F g)) = proj 4 F g
    rw [dualAut_proj, conjAut_proj, conj_inv_transpose_of_symp A g hsymp]
  · rw [hmul, hzb]
    intro h
    obtain ⟨c, -, hc⟩ := proj_eq_exists h
    have e := congrFun (congrFun hc 0) 0
    rw [hz, hw] at e
    simp [wMat] at e
  · rw [hmul, hzb, ← map_mul, ← map_mul]
    apply QuotientGroup.eq.mpr
    rw [mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    have hinv : (w * r)⁻¹ = r * w := by
      rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right hw2, inv_eq_of_mul_eq_one_right hz2]
    rw [hinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hz, hw,
      z_mul_w_sq hm hn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end CFSG.ClassicalInvolution.Asc77.CX.CX4.L4
