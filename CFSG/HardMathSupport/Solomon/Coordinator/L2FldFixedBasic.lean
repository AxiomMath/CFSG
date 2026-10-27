module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (StatedProj StatedSL StatedScalars)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

section

variable {F : Type} [Field F]

@[expose] def l2fld_xGL (a : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], !![1, -a; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem l2fld_xGL_apply_val (a : F) : ((l2fld_xGL a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    !![1, a; 0, 1] := rfl

theorem l2fld_xGL_mem (a : F) : l2fld_xGL a ∈ StatedSL 2 F :=
  Subgroup.subset_closure (by simp [l2fld_xGL_apply_val, Matrix.det_fin_two])

theorem l2fld_mk_eq_iff_smul (A B : ↥(StatedSL 2 F)) :
    (QuotientGroup.mk A : StatedProj (StatedSL 2 F)) = QuotientGroup.mk B ↔
      ∃ c : Fˣ, ((B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (c : F) • ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h1 : (A : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹ * (B : Matrix.GeneralLinearGroup (Fin 2) F) =
        Matrix.GeneralLinearGroup.scalar (Fin 2) c := hc.symm
    have h2 : (B : Matrix.GeneralLinearGroup (Fin 2) F) =
        (A : Matrix.GeneralLinearGroup (Fin 2) F) * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      rw [← h1]; group
    rw [h2, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have hA : (A : Matrix.GeneralLinearGroup (Fin 2) F) * (A : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹ = 1 :=
      mul_inv_cancel _
    show _ = ((A : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹ * (B : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix.GeneralLinearGroup (Fin 2) F).val
    rw [Units.val_mul, hc, Matrix.mul_smul]
    have : ((A : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F).val *
        ((A : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.smul_one_eq_diagonal]

theorem l2fld_sigma_pow_three {σ : F ≃+* F} {φ : MulAut (StatedProj (StatedSL 2 F))}
    (hφ : IsEntrywiseAutPSLn 2 σ φ) (hφ3 : φ ^ 3 = 1) : σ ^ 3 = 1 := by
  ext a
  have step : ∀ b : F, φ (QuotientGroup.mk ⟨l2fld_xGL b, l2fld_xGL_mem b⟩) =
      QuotientGroup.mk ⟨l2fld_xGL (σ b), l2fld_xGL_mem _⟩ := by
    intro b
    apply hφ
    ext i j
    fin_cases i <;> fin_cases j <;> simp [l2fld_xGL_apply_val]
  have h3 : (φ ^ 3) (QuotientGroup.mk ⟨l2fld_xGL a, l2fld_xGL_mem a⟩) =
      QuotientGroup.mk ⟨l2fld_xGL (σ (σ (σ a))), l2fld_xGL_mem _⟩ := by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, step]
  rw [hφ3, MulAut.one_apply] at h3
  obtain ⟨c, hc⟩ := (l2fld_mk_eq_iff_smul _ _).1 h3
  have h00 := congrFun (congrFun hc 0) 0
  have h01 := congrFun (congrFun hc 0) 1
  simp only [l2fld_xGL_apply_val, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    mul_one] at h00 h01
  have hc1 : (c : F) = 1 := h00.symm
  rw [hc1, one_mul] at h01
  show (σ ^ 3) a = a
  calc (σ ^ 3) a = σ (σ (σ a)) := by simp [pow_succ]
    _ = a := h01

theorem l2fld_sigma_ne_one {σ : F ≃+* F} {φ : MulAut (StatedProj (StatedSL 2 F))}
    (hφ : IsEntrywiseAutPSLn 2 σ φ) (hφ1 : φ ≠ 1) : σ ≠ 1 := by
  intro hσ
  apply hφ1
  ext x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.one_apply]
  apply hφ A A
  subst hσ
  ext i j
  simp

end

end CFSG.HardMathSupport.Solomon.Coordinator
