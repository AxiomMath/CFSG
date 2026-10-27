module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesWeir
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

abbrev SL2F3 : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 3)

@[expose] noncomputable def detForm : QuadraticForm (ZMod 3) Mat2 :=
  QuadraticMap.linMulLin (Matrix.entryLinearMap (ZMod 3) (ZMod 3) 0 0)
      (Matrix.entryLinearMap (ZMod 3) (ZMod 3) 1 1) -
    QuadraticMap.linMulLin (Matrix.entryLinearMap (ZMod 3) (ZMod 3) 0 1)
      (Matrix.entryLinearMap (ZMod 3) (ZMod 3) 1 0)

theorem detForm_apply (X : Mat2) : detForm X = X.det := by
  simp [detForm, QuadraticMap.linMulLin_apply, Matrix.det_fin_two]

theorem finrank_mat2 : Module.finrank (ZMod 3) Mat2 = 4 := by
  simp [Module.finrank_matrix]

theorem detForm_nondegenerate : detForm.Nondegenerate := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, Submodule.eq_bot_iff]
  intro X hX
  obtain ⟨h0, h1⟩ := QuadraticMap.mem_radical_iff'.mp hX
  have key : ∀ a b c d : ZMod 3, a * d - b * c = 0 →
      (∀ a' b' c' d' : ZMod 3,
        (a + a') * (d + d') - (b + b') * (c + c') = a' * d' - b' * c') →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
    decide +kernel
  have h1' : ∀ a' b' c' d' : ZMod 3,
      (X 0 0 + a') * (X 1 1 + d') - (X 0 1 + b') * (X 1 0 + c') = a' * d' - b' * c' := by
    intro a' b' c' d'
    have h := h1 !![a', b'; c', d']
    rw [detForm_apply, detForm_apply] at h
    simpa [Matrix.det_fin_two] using h
  rw [detForm_apply, Matrix.det_fin_two] at h0
  obtain ⟨ha, hb, hc, hd⟩ := key _ _ _ _ h0 h1'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem quadSign_detForm : quadSign detForm = 1 := by
  let ι : (Fin 2 → ZMod 3) →ₗ[ZMod 3] Mat2 :=
    { toFun := fun v => !![v 0, v 1; 0, 0]
      map_add' := by
        intro v w
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      map_smul' := by
        intro c v
        ext i j
        fin_cases i <;> fin_cases j <;> simp }
  have hinj : Function.Injective ι := by
    intro v w h
    have h0 := congrFun (congrFun h 0) 0
    have h1 := congrFun (congrFun h 0) 1
    funext i
    fin_cases i
    · simpa [ι] using h0
    · simpa [ι] using h1
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType detForm := by
    refine ⟨LinearMap.range ι, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, finrank_mat2]
      simp
    · rintro x ⟨v, rfl⟩
      rw [detForm_apply]
      simp [ι, Matrix.det_fin_two]
  exact (isPlusType_iff_quadSign_eq_one detForm_nondegenerate (d := 2)
    (by rw [finrank_mat2])).mp hplus

@[expose] noncomputable def mulLeftEquiv (A : SL2F3) : Mat2 ≃ₗ[ZMod 3] Mat2 :=
  LinearEquiv.ofLinear (LinearMap.mulLeft (ZMod 3) (A : Mat2))
    (LinearMap.mulLeft (ZMod 3) ((A⁻¹ : SL2F3) : Mat2))
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
        ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul])
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply,
        ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul])

@[expose] noncomputable def mulRightEquiv (B : SL2F3) : Mat2 ≃ₗ[ZMod 3] Mat2 :=
  LinearEquiv.ofLinear (LinearMap.mulRight (ZMod 3) ((B⁻¹ : SL2F3) : Mat2))
    (LinearMap.mulRight (ZMod 3) (B : Mat2))
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
        Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one])
    (by
      ext X : 1
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
        Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one])

theorem mulLeftEquiv_mem (A : SL2F3) :
    mulLeftEquiv A ∈ TauCeti.QuadraticMap.orthogonalGroup detForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  rw [detForm_apply, detForm_apply]
  change ((A : Mat2) * X).det = X.det
  rw [Matrix.det_mul, A.det_coe, one_mul]

theorem mulRightEquiv_mem (B : SL2F3) :
    mulRightEquiv B ∈ TauCeti.QuadraticMap.orthogonalGroup detForm := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro X
  rw [detForm_apply, detForm_apply]
  change (X * ((B⁻¹ : SL2F3) : Mat2)).det = X.det
  rw [Matrix.det_mul, (B⁻¹ : SL2F3).det_coe, mul_one]

@[expose] noncomputable def leftMulHom : SL2F3 →* OGroup detForm where
  toFun A := ⟨mulLeftEquiv A, mulLeftEquiv_mem A⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change (1 : Mat2) * X = X
    exact Matrix.one_mul X
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change ((A * B : SL2F3) : Mat2) * X = (A : Mat2) * ((B : Mat2) * X)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

@[expose] noncomputable def rightMulHom : SL2F3 →* OGroup detForm where
  toFun B := ⟨mulRightEquiv B, mulRightEquiv_mem B⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change X * (((1 : SL2F3)⁻¹ : SL2F3) : Mat2) = X
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    change X * (((A * B : SL2F3)⁻¹ : SL2F3) : Mat2) =
      (X * (((B⁻¹ : SL2F3)) : Mat2)) * (((A⁻¹ : SL2F3)) : Mat2)
    rw [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

theorem leftMulHom_apply (A : SL2F3) (X : Mat2) :
    ((leftMulHom A : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X = (A : Mat2) * X := rfl

theorem rightMulHom_apply (B : SL2F3) (X : Mat2) :
    ((rightMulHom B : OGroup detForm) : Mat2 ≃ₗ[ZMod 3] Mat2) X = X * ((B⁻¹ : SL2F3) : Mat2) :=
  rfl

theorem leftMulHom_injective : Function.Injective leftMulHom := by
  intro A B h
  have h1 := leftMulHom_apply A 1
  rw [h, leftMulHom_apply B 1] at h1
  simp only [Matrix.mul_one] at h1
  exact Subtype.ext h1.symm

theorem leftMulHom_mul_rightMulHom_comm (A B : SL2F3) :
    leftMulHom A * rightMulHom B = rightMulHom B * leftMulHom A := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  change (A : Mat2) * (X * ((B⁻¹ : SL2F3) : Mat2)) = ((A : Mat2) * X) * ((B⁻¹ : SL2F3) : Mat2)
  rw [Matrix.mul_assoc]

theorem leftMulHom_eq_piOrth {A : SL2F3} (hA : (A : Mat2) = -1) :
    leftMulHom A = piOrth detForm := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [coe_piOrth_apply]
  change (A : Mat2) * X = -X
  rw [hA, neg_mul, Matrix.one_mul]

theorem exists_sl2f3_eq_neg_one : ∃ A : SL2F3, (A : Mat2) = -1 := by
  refine ⟨⟨-1, ?_⟩, rfl⟩
  rw [Matrix.det_neg, Matrix.det_one]
  decide

end CFSG.OddStandard.SmallF3.Omega
