module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4PSpL4

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  CFSG.ComponentClassification.CatFactsL4U4.StabL CFSG.ComponentClassification.CatFactsL4U4.PSpL

theorem exists_sp4_hom_of_alt_L4 {F : Type} [Field F] (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F)
    (hA : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -A) :
    ∃ ϖ : ↥(StatedSp 2 F) →* projectiveSL 4 F,
      (∀ x, (conjAut 4 F A * dualAut 4 F) (ϖ x) = ϖ x) ∧
      ∀ x, ϖ x = 1 → (x : GL (Fin 2 ⊕ Fin 2) F) ∈ StatedScalars (Fin 2 ⊕ Fin 2) F := by
  classical
  set R := ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hRdef
  have hAR : (A : Matrix (Fin 4) (Fin 4) F) * R = 1 := by
    rw [hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRt : Rᵀ = -R := by
    have h1 : Rᵀ * (A : Matrix (Fin 4) (Fin 4) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hRdef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.transpose_one]
    rw [hA, Matrix.mul_neg, neg_eq_iff_eq_neg] at h1
    calc Rᵀ = Rᵀ * ((A : Matrix (Fin 4) (Fin 4) F) * R) := by rw [hAR, Matrix.mul_one]
      _ = -R := by rw [← Matrix.mul_assoc, h1, Matrix.neg_mul, Matrix.one_mul]
  have hRu : IsUnit R.det := by
    rw [hRdef, ← GeneralLinearGroup.val_det_apply]
    exact Units.isUnit _
  obtain ⟨P, hP⟩ := exists_transpose_mul_mul_eq_omg h2 hRt hRu
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let ι : StatedSp 2 F →* SpecialLinearGroup (Fin 4) F :=
    { toFun := fun M => ⟨((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
        by
          rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, det_mul, det_mul,
            (spGL_spec F M).2, mul_one, ← det_mul, hPP, det_one]⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun M N => by
        apply Subtype.ext
        show ((MulAut.conj P (spGL F (M * N)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((MulAut.conj P (spGL F N) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        rw [map_mul, map_mul, Units.val_mul] }
  have hι : ∀ M, (ι M : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * ((spGL F M : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) := fun M => by
    change ((MulAut.conj P (spGL F M) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = _
    rw [MulAut.conj_apply, Units.val_mul, Units.val_mul]
  refine ⟨(proj 4 F).comp ι, ?_, ?_⟩
  · intro x
    rw [MonoidHom.comp_apply]
    apply conjAut_dualAut_proj_of_transpose_mul_mul A
    rw [hι]
    apply conj_transpose_mul_mul hPP
    rw [← hRdef, hP]
    exact (spGL_spec F x).1
  · intro x hx
    rw [MonoidHom.comp_apply, proj_eq_one_iff, mem_scalars] at hx
    obtain ⟨c, -, hc⟩ := hx
    apply mem_statedScalars_of_spGL (c := (c : F))
    have e1 : (P : Matrix (Fin 4) (Fin 4) F) *
        ((spGL F x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) = (c : F) • 1 := by
      rw [← hι, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hPi : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc ((spGL F x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F) * ((P : Matrix (Fin 4) (Fin 4) F) *
          ((spGL F x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) F)) * (P : Matrix (Fin 4) (Fin 4) F) := by
          simp only [← Matrix.mul_assoc]
          rw [hPi, Matrix.one_mul, Matrix.mul_assoc, hPi, Matrix.mul_one]
      _ = (c : F) • 1 := by
          rw [e1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPi]

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
