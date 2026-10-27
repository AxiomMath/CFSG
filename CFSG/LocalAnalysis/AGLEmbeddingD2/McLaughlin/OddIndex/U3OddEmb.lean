module

public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary

variable {F : Type} [Field F]

@[expose] def embMat (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![M 0 0, 0, M 0 1; 0, 1, 0; M 1 0, 0, M 1 1]

theorem embMat_mul (M N : Matrix (Fin 2) (Fin 2) F) : embMat (M * N) = embMat M * embMat N := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem embMat_one : embMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat]

theorem det_embMat (M : Matrix (Fin 2) (Fin 2) F) : (embMat M).det = M.det := by
  simp [embMat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem embMat_injective : Function.Injective (embMat (F := F)) := by
  intro M N h
  ext i j
  have := congrFun (congrFun h (if i = 0 then 0 else 2)) (if j = 0 then 0 else 2)
  fin_cases i <;> fin_cases j <;> simpa [embMat] using this

theorem embMat_isometry (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F)
    (h : conjTr σ M * antidiag 2 * M = antidiag 2) :
    conjTr σ (embMat M) * antidiag 3 * embMat M = antidiag 3 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMat, conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first | exact e00 | exact e01 | exact e10 | exact e11

@[expose] def embGLHom : GL (Fin 2) F →* GL (Fin 3) F where
  toFun M := ⟨embMat M, embMat (M⁻¹ : GL (Fin 2) F), by
    rw [← embMat_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, embMat_one], by
    rw [← embMat_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, embMat_one]⟩
  map_one' := Units.ext (by simp [embMat_one])
  map_mul' M N := Units.ext (by simp [embMat_mul])

theorem coe_embGLHom (M : GL (Fin 2) F) :
    ((embGLHom M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = embMat (M : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem embGLHom_injective : Function.Injective (embGLHom (F := F)) := by
  intro M N h
  exact Units.ext (embMat_injective (congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h))

theorem embGLHom_mem_SU (σ : F ≃+* F) {M : GL (Fin 2) F} (hM : M ∈ SU σ 2) :
    embGLHom M ∈ SU σ 3 := by
  refine ⟨?_, ?_⟩
  · rw [coe_embGLHom, det_embMat]; exact hM.1
  · rw [coe_embGLHom]; exact embMat_isometry σ _ hM.2

@[expose] def embSU (σ : F ≃+* F) : SU σ 2 →* SU σ 3 :=
  (embGLHom.comp (SU σ 2).subtype).codRestrict _ fun M => embGLHom_mem_SU σ M.2

theorem embSU_injective (σ : F ≃+* F) : Function.Injective (embSU σ) := by
  intro M N h
  exact Subtype.ext (embGLHom_injective (congrArg Subtype.val h))

theorem coe_embSU (σ : F ≃+* F) (M : SU σ 2) :
    (((embSU σ M : SU σ 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      embMat (((M : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] def mat3 {σ : F ≃+* F} (x : SU σ 3) : Matrix (Fin 3) (Fin 3) F :=
  ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem mat3_mul {σ : F ≃+* F} (x y : SU σ 3) : mat3 (x * y) = mat3 x * mat3 y := rfl

theorem mat3_injective {σ : F ≃+* F} : Function.Injective (mat3 (σ := σ)) := fun _ _ h =>
  Subtype.ext (Units.ext h)

theorem embMat_of_blockForm {m : Matrix (Fin 3) (Fin 3) F} (h01 : m 0 1 = 0) (h10 : m 1 0 = 0)
    (h12 : m 1 2 = 0) (h21 : m 2 1 = 0) (h11 : m 1 1 = 1) :
    m = embMat !![m 0 0, m 0 2; m 2 0, m 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embMat, h01, h10, h12, h21, h11]

theorem isometry_of_embMat (σ : F ≃+* F) (M : Matrix (Fin 2) (Fin 2) F)
    (h : conjTr σ (embMat M) * antidiag 3 * embMat M = antidiag 3) :
    conjTr σ M * antidiag 2 * M = antidiag 2 := by
  have e00 := congrFun (congrFun h 0) 0
  have e02 := congrFun (congrFun h 0) 2
  have e20 := congrFun (congrFun h 2) 0
  have e22 := congrFun (congrFun h 2) 2
  simp [embMat, conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three] at e00 e02 e20 e22
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | exact e00 | exact e02 | exact e20 | exact e22

theorem mem_range_embSU_of_blockForm {σ : F ≃+* F} {x : SU σ 3} (h01 : mat3 x 0 1 = 0)
    (h10 : mat3 x 1 0 = 0) (h12 : mat3 x 1 2 = 0) (h21 : mat3 x 2 1 = 0) (h11 : mat3 x 1 1 = 1) :
    x ∈ (embSU σ).range := by
  set M : Matrix (Fin 2) (Fin 2) F := !![mat3 x 0 0, mat3 x 0 2; mat3 x 2 0, mat3 x 2 2] with hM
  have hx : mat3 x = embMat M := embMat_of_blockForm h01 h10 h12 h21 h11
  have hdet : M.det = 1 := by
    rw [← det_embMat, ← hx]
    exact x.2.1
  have hiso : conjTr σ M * antidiag 2 * M = antidiag 2 := by
    apply isometry_of_embMat σ M
    rw [← hx]
    exact x.2.2
  refine ⟨⟨Matrix.SpecialLinearGroup.toGL (⟨M, hdet⟩ : Matrix.SpecialLinearGroup (Fin 2) F),
    hdet, hiso⟩, ?_⟩
  apply mat3_injective
  exact hx.symm

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
