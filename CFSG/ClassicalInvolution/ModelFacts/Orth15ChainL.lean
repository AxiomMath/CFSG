module

public import CFSG.ClassicalInvolution.Models.LinearPairs.RootSL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

namespace ChainL

variable {F : Type} [Field F]


theorem blockMat_three (A : Matrix (Fin 2) (Fin 2) F) :
    blockMat 3 0 A = !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem proj_eq_exists {a b : SL(3, F)} (h : proj 3 F a = proj 3 F b) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧
      (b : Matrix (Fin 3) (Fin 3) F) = (c : F) • (a : Matrix (Fin 3) (Fin 3) F) := by
  have h1 : a⁻¹ * b ∈ scalars 3 F := QuotientGroup.eq.mp h
  obtain ⟨c, hc, hcm⟩ := mem_scalars.mp h1
  refine ⟨c, hc, ?_⟩
  have hb : a * (a⁻¹ * b) = b := by group
  have : (b : Matrix (Fin 3) (Fin 3) F) = (a : Matrix (Fin 3) (Fin 3) F) *
      ((a⁻¹ * b : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hb]
  rw [this, hcm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

theorem alpha_proj_zero (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
        (Matrix.SpecialLinearGroup.map σ.toRingHom g)) := by
  show conjAut 3 F A (fieldAut 3 F σ (proj 3 F g)) = _
  rw [fieldAut_proj, conjAut_proj]

@[expose] def e01 (t : F) : SL(3, F) :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def e10 (t : F) : SL(3, F) :=
  ⟨!![1, 0, 0; t, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def e02 (t : F) : SL(3, F) :=
  ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def xN : SL(3, F) :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem e01_mem (hn : 2 ≤ 3) (t : F) : e01 t ∈ rootSL2 F hn := by
  let A : SL(2, F) := ⟨!![1, t; 0, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, A]




theorem xN_mem (hn : 2 ≤ 3) : (xN : SL(3, F)) ∈ rootSL2 F hn := by
  let A : SL(2, F) := ⟨!![-1, 0; 0, -1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xN, A]

theorem e10_mem (hn : 2 ≤ 3) (t : F) : e10 t ∈ rootSL2 F hn := by
  let A : SL(2, F) := ⟨!![1, 0; t, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e10, A]

theorem key0 (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num),
      (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F r) = proj 3 F r)
    {r : SL(3, F)} (hr : r ∈ rootSL2 F (show 2 ≤ 3 by norm_num)) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ (r : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F).map σ) := by
  have h := hfix r hr
  rw [alpha_proj_zero] at h
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists h
  refine ⟨c, hc, ?_⟩
  have h1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (Matrix.SpecialLinearGroup.map σ.toRingHom r) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  have hNM : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1] at hcm
  calc (r : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
      = ((c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F).map σ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) * (A : Matrix (Fin 3) (Fin 3) F) := by
        rw [← hcm]
    _ = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) * (r : Matrix (Fin 3) (Fin 3) F).map σ) := by
        rw [Matrix.smul_mul, Matrix.mul_assoc, hNM, Matrix.mul_one]


theorem case0 (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num),
      (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F r) = proj 3 F r) :
    σ = RingEquiv.refl F ∧ ∃ a w : F, a ≠ 0 ∧ w ≠ 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, a, 0; 0, 0, w] := by
  set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
  set N : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp A.isUnit
    exact this.ne_zero
  have hxσ : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [xN]
  obtain ⟨c, hc, hxM⟩ := key0 A σ hfix (xN_mem (show 2 ≤ 3 by norm_num))
  rw [hxσ] at hxM
  have hxx : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [xN, Matrix.mul_apply, Fin.sum_univ_three]
  have hc2 : (c : F) ^ 2 = 1 := by
    have e1 : M = ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) := by
      rw [← Matrix.mul_assoc, hxx, Matrix.one_mul]
    have e2 : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) = ((c : F) ^ 2) • M := by
      rw [hxM, Matrix.mul_smul, ← Matrix.mul_assoc, hxM, Matrix.smul_mul, Matrix.mul_assoc,
        hxx, Matrix.mul_one, smul_smul, pow_two]
    have e3 : ((c : F) ^ 2) • M = M := by rw [← e2, ← e1]
    have e4 : ((c : F) ^ 2) • (M * N) = M * N := by rw [← Matrix.smul_mul, e3]
    rw [hMN] at e4
    have e5 := congrFun (congrFun e4 0) 0
    simpa using e5
  have hc1 : c = 1 := by
    have h2' : c ^ 2 = 1 := Units.ext (by simpa using hc2)
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc, h2']; simp
  have hxM1 : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M =
      M * ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    simpa [hc1] using hxM
  have e02 := congrFun (congrFun hxM1 0) 2
  have e12 := congrFun (congrFun hxM1 1) 2
  have e20 := congrFun (congrFun hxM1 2) 0
  have e21 := congrFun (congrFun hxM1 2) 1
  simp [xN, Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21
  have two_mul_eq : ∀ x : F, x + x = 0 → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  have m02 : M 0 2 = 0 := two_mul_eq _ (by linear_combination -e02)
  have m12 : M 1 2 = 0 := two_mul_eq _ (by linear_combination -e12)
  have m20 : M 2 0 = 0 := two_mul_eq _ (by linear_combination e20)
  have m21 : M 2 1 = 0 := two_mul_eq _ (by linear_combination e21)
  have hM22 : M 2 2 ≠ 0 := by
    have h := congrFun (congrFun hMN 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, m20, m21] at h
    intro h0
    rw [h0] at h
    simp at h
  have hσe01 : ∀ t : F, ((e01 t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((e01 (σ t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    intro t; ext i j; fin_cases i <;> fin_cases j <;> simp [e01]
  have hrel : ∀ t : F, ((e01 t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M =
      M * ((e01 (σ t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    intro t
    obtain ⟨ct, hct, h⟩ := key0 A σ hfix (e01_mem (show 2 ≤ 3 by norm_num) t)
    rw [hσe01] at h
    have e22 := congrFun (congrFun h 2) 2
    simp [e01, Matrix.mul_apply, Fin.sum_univ_three] at e22
    have hct1 : (ct : F) = 1 := by
      have : (1 - (ct : F)) * M 2 2 = 0 := by linear_combination e22
      have := (mul_eq_zero.mp this).resolve_right hM22
      linear_combination -this
    rw [hct1, one_smul] at h
    exact h
  have hone := hrel 1
  rw [show σ 1 = 1 from map_one σ] at hone
  have f00 := congrFun (congrFun hone 0) 0
  have f01 := congrFun (congrFun hone 0) 1
  simp [e01, Matrix.mul_apply, Fin.sum_univ_three] at f00 f01
  have m10 : M 1 0 = 0 := by linear_combination f00
  have m11 : M 1 1 = M 0 0 := by linear_combination f01
  have hdet' : M.det = M 0 0 * M 1 1 * M 2 2 := by
    rw [Matrix.det_fin_three]
    simp [m02, m12, m20, m21, m10]
  have hM00 : M 0 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [hdet', h0]
    simp
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have g01 := congrFun (congrFun (hrel t) 0) 1
    simp [e01, Matrix.mul_apply, Fin.sum_univ_three] at g01
    rw [m11] at g01
    have : (t - σ t) * M 0 0 = 0 := by linear_combination g01
    have := (mul_eq_zero.mp this).resolve_right hM00
    simpa using (sub_eq_zero.mp this).symm
  have hσe10 : ((e10 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).map σ =
      ((e10 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [e10]
  obtain ⟨c', hc', h'⟩ := key0 A σ hfix (e10_mem (show 2 ≤ 3 by norm_num) 1)
  rw [hσe10] at h'
  have g22 := congrFun (congrFun h' 2) 2
  simp [e10, Matrix.mul_apply, Fin.sum_univ_three] at g22
  have hc'1 : (c' : F) = 1 := by
    have : (1 - (c' : F)) * M 2 2 = 0 := by linear_combination g22
    have := (mul_eq_zero.mp this).resolve_right hM22
    linear_combination -this
  rw [hc'1, one_smul] at h'
  have g00 := congrFun (congrFun h' 0) 0
  simp [e10, Matrix.mul_apply, Fin.sum_univ_three] at g00
  have m01 : M 0 1 = 0 := g00
  refine ⟨hσ, M 0 0, M 2 2, hM00, hM22, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m01, m02, m10, m11, m12, m20, m21]




theorem alpha_proj_one (A : GL (Fin 3) F) (σ : F ≃+* F) (g : SL(3, F)) :
    (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F g) =
      proj 3 F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
        (Matrix.SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose)) := by
  show conjAut 3 F A (fieldAut 3 F σ (dualAut 3 F (proj 3 F g))) = _
  rw [dualAut_proj, fieldAut_proj, conjAut_proj]

theorem coe_inv_transpose_e01 (t : F) :
    (((e01 t)⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; -t, 1, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e01, Matrix.adjugate_fin_three]

theorem coe_inv_transpose_e10 (t : F) :
    (((e10 t)⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![1, -t, 0; 0, 1, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e10, Matrix.adjugate_fin_three]

theorem coe_inv_transpose_xN :
    (((xN : SL(3, F))⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xN, Matrix.adjugate_fin_three]

theorem key1 (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num),
      (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F r) = proj 3 F r)
    {r : SL(3, F)} (hr : r ∈ rootSL2 F (show 2 ≤ 3 by norm_num)) :
    ∃ c : Fˣ, c ^ 3 = 1 ∧ (r : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
        (((r⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F)).map σ) := by
  have h := hfix r hr
  rw [alpha_proj_one] at h
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists h
  refine ⟨c, hc, ?_⟩
  have h1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      (Matrix.SpecialLinearGroup.map σ.toRingHom (r⁻¹).transpose) : SL(3, F)) :
        Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) *
        (((r⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F)).map σ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  have hNM : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1] at hcm
  calc (r : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F)
      = ((c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
          (((r⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F)).map σ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) * (A : Matrix (Fin 3) (Fin 3) F) := by
        rw [← hcm]
    _ = (c : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
        (((r⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F)).map σ) := by
        rw [Matrix.smul_mul, Matrix.mul_assoc, hNM, Matrix.mul_one]


theorem case1 (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num),
      (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F r) = proj 3 F r) :
    σ = RingEquiv.refl F ∧ ∃ u w : F, u ≠ 0 ∧ w ≠ 0 ∧
      (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w] := by
  set M : Matrix (Fin 3) (Fin 3) F := (A : Matrix (Fin 3) (Fin 3) F) with hM
  set N : Matrix (Fin 3) (Fin 3) F := ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hN
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet : M.det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det M).mp A.isUnit
    exact this.ne_zero
  have hxσ : ((((xN : SL(3, F))⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F)).map σ =
      ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [coe_inv_transpose_xN]
    ext i j; fin_cases i <;> fin_cases j <;> simp [xN]
  obtain ⟨c, hc, hxM⟩ := key1 A σ hfix (xN_mem (show 2 ≤ 3 by norm_num))
  rw [hxσ] at hxM
  have hxx : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [xN, Matrix.mul_apply, Fin.sum_univ_three]
  have hc2 : (c : F) ^ 2 = 1 := by
    have e1 : M = ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) := by
      rw [← Matrix.mul_assoc, hxx, Matrix.one_mul]
    have e2 : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        (((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) = ((c : F) ^ 2) • M := by
      rw [hxM, Matrix.mul_smul, ← Matrix.mul_assoc, hxM, Matrix.smul_mul, Matrix.mul_assoc,
        hxx, Matrix.mul_one, smul_smul, pow_two]
    have e3 : ((c : F) ^ 2) • M = M := by rw [← e2, ← e1]
    have e4 : ((c : F) ^ 2) • (M * N) = M * N := by rw [← Matrix.smul_mul, e3]
    rw [hMN] at e4
    have e5 := congrFun (congrFun e4 0) 0
    simpa using e5
  have hc1 : c = 1 := by
    have h2' : c ^ 2 = 1 := Units.ext (by simpa using hc2)
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc, h2']; simp
  have hxM1 : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M =
      M * ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    simpa [hc1] using hxM
  have e02 := congrFun (congrFun hxM1 0) 2
  have e12 := congrFun (congrFun hxM1 1) 2
  have e20 := congrFun (congrFun hxM1 2) 0
  have e21 := congrFun (congrFun hxM1 2) 1
  simp [xN, Matrix.mul_apply, Fin.sum_univ_three] at e02 e12 e20 e21
  have two_mul_eq : ∀ x : F, x + x = 0 → x = 0 := fun x hx => by
    have : (2 : F) * x = 0 := by linear_combination hx
    exact (mul_eq_zero.mp this).resolve_left h2
  have m02 : M 0 2 = 0 := two_mul_eq _ (by linear_combination -e02)
  have m12 : M 1 2 = 0 := two_mul_eq _ (by linear_combination -e12)
  have m20 : M 2 0 = 0 := two_mul_eq _ (by linear_combination e20)
  have m21 : M 2 1 = 0 := two_mul_eq _ (by linear_combination e21)
  have hM22 : M 2 2 ≠ 0 := by
    have h := congrFun (congrFun hMN 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, m20, m21] at h
    intro h0
    rw [h0] at h
    simp at h
  have hσe01 : ∀ t : F, (((e01 t : SL(3, F))⁻¹ : SL(3, F)).transpose :
      Matrix (Fin 3) (Fin 3) F).map σ = !![1, 0, 0; -σ t, 1, 0; 0, 0, 1] := by
    intro t
    rw [coe_inv_transpose_e01]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hrel : ∀ t : F, ((e01 t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M =
      M * !![1, 0, 0; -σ t, 1, 0; 0, 0, 1] := by
    intro t
    obtain ⟨ct, hct, h⟩ := key1 A σ hfix (e01_mem (show 2 ≤ 3 by norm_num) t)
    rw [hσe01] at h
    have e22 := congrFun (congrFun h 2) 2
    simp [e01, Matrix.mul_apply, Fin.sum_univ_three] at e22
    have hct1 : (ct : F) = 1 := by
      have : (1 - (ct : F)) * M 2 2 = 0 := by linear_combination e22
      have := (mul_eq_zero.mp this).resolve_right hM22
      linear_combination -this
    rw [hct1, one_smul] at h
    exact h
  have hone := hrel 1
  rw [show σ 1 = 1 from map_one σ] at hone
  have f01 := congrFun (congrFun hone 0) 1
  have f00 := congrFun (congrFun hone 0) 0
  simp [e01, Matrix.mul_apply, Fin.sum_univ_three] at f01 f00
  have m11 : M 1 1 = 0 := by linear_combination f01
  have m10 : M 1 0 = -M 0 1 := by linear_combination f00
  have hσe10 : (((e10 1 : SL(3, F))⁻¹ : SL(3, F)).transpose :
      Matrix (Fin 3) (Fin 3) F).map σ = !![1, -1, 0; 0, 1, 0; 0, 0, 1] := by
    rw [coe_inv_transpose_e10]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨c', hc', h'⟩ := key1 A σ hfix (e10_mem (show 2 ≤ 3 by norm_num) 1)
  rw [hσe10] at h'
  have g22 := congrFun (congrFun h' 2) 2
  simp [e10, Matrix.mul_apply, Fin.sum_univ_three] at g22
  have hc'1 : (c' : F) = 1 := by
    have : (1 - (c' : F)) * M 2 2 = 0 := by linear_combination g22
    have := (mul_eq_zero.mp this).resolve_right hM22
    linear_combination -this
  rw [hc'1, one_smul] at h'
  have g10 := congrFun (congrFun h' 1) 0
  simp [e10, Matrix.mul_apply, Fin.sum_univ_three] at g10
  have m00 : M 0 0 = 0 := by linear_combination g10
  have hdet' : M.det = M 0 1 * M 0 1 * M 2 2 := by
    rw [Matrix.det_fin_three]
    simp [m02, m12, m20, m21, m11, m10, m00]
  have hM01 : M 0 1 ≠ 0 := by
    intro h0
    apply hdet
    rw [hdet', h0]
    simp
  have hσ : σ = RingEquiv.refl F := by
    ext t
    have g00 := congrFun (congrFun (hrel t) 0) 0
    simp [e01, Matrix.mul_apply, Fin.sum_univ_three, m10] at g00
    have : (t - σ t) * M 0 1 = 0 := by linear_combination g00
    have := (mul_eq_zero.mp this).resolve_right hM01
    simpa using (sub_eq_zero.mp this).symm
  refine ⟨hσ, M 0 1, M 2 2, hM01, hM22, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [m00, m02, m10, m11, m12, m20, m21]




@[expose] def e21 (t : F) : SL(3, F) :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, t, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_inv_transpose_e02 (t : F) :
    (((e02 t)⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; -t, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e02, Matrix.adjugate_fin_three]

theorem coe_inv_transpose_e21 (t : F) :
    (((e21 t)⁻¹ : SL(3, F)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, -t; 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e21, Matrix.adjugate_fin_three]

theorem coe_slConj (A : GL (Fin 3) F) (g : SL(3, F)) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix 3 F A g

theorem inv_matrix_diag (A : GL (Fin 3) F) (a w : F) (ha : a ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, a, 0; 0, 0, w]) :
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![a⁻¹, 0, 0; 0, a⁻¹, 0; 0, 0, w⁻¹] := by
  have h2 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h0 : (!![a, 0, 0; 0, a, 0; 0, 0, w] : Matrix (Fin 3) (Fin 3) F) *
      !![a⁻¹, 0, 0; 0, a⁻¹, 0; 0, 0, w⁻¹] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ha, hw]
  calc ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        !![a⁻¹, 0, 0; 0, a⁻¹, 0; 0, 0, w⁻¹] := by
        rw [hA, Matrix.mul_assoc, h0, Matrix.mul_one]
    _ = !![a⁻¹, 0, 0; 0, a⁻¹, 0; 0, 0, w⁻¹] := by rw [h2, Matrix.one_mul]

theorem slConj_scalar_diag (A : GL (Fin 3) F) (a w : F) (ha : a ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, a, 0; 0, 0, w]) (g : SL(3, F)) :
    ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A g : SL(3, F)) :
      Matrix (Fin 3) (Fin 3) F) =
    !![g 0 0, g 0 1, a * g 0 2 * w⁻¹; g 1 0, g 1 1, a * g 1 2 * w⁻¹;
      w * g 2 0 * a⁻¹, w * g 2 1 * a⁻¹, g 2 2] := by
  rw [coe_slConj, inv_matrix_diag A a w ha hw hA, hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp <;>
    field_simp

theorem slConj_e02 (A : GL (Fin 3) F) (a w : F) (ha : a ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, a, 0; 0, 0, w]) (t : F) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A (e02 t) =
      e02 (a * t * w⁻¹) := by
  apply Subtype.ext
  rw [slConj_scalar_diag A a w ha hw hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e02]

theorem coe_xN_conj (g : SL(3, F)) :
    ((xN * g * xN⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      !![g 0 0, g 0 1, -g 0 2; g 1 0, g 1 1, -g 1 2; -g 2 0, -g 2 1, g 2 2] := by
  have hxx : (xN : SL(3, F)) * xN = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [xN, Matrix.mul_apply, Fin.sum_univ_three]
  have hxinv : (xN : SL(3, F))⁻¹ = xN := inv_eq_of_mul_eq_one_right hxx
  rw [hxinv]
  have hx : ((xN : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := rfl
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;> simp


theorem fin0 (A : GL (Fin 3) F) (a w : F) (ha : a ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![a, 0, 0; 0, a, 0; 0, 0, w])
    (hα : conjAut 3 F A * conjAut 3 F A = 1) :
    (∀ g : SL(3, F), conjAut 3 F A (proj 3 F g) = proj 3 F g) ∨
      (∀ g : SL(3, F), conjAut 3 F A (proj 3 F g) = proj 3 F (xN * g * xN⁻¹)) := by
  have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (proj 3 F (e02 1))) hα
  simp only [MulAut.mul_apply, MulAut.one_apply, conjAut_proj] at h
  rw [slConj_e02 A a w ha hw hA, slConj_e02 A a w ha hw hA] at h
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists h
  have e1 := congrFun (congrFun hcm 0) 0
  have e2 := congrFun (congrFun hcm 0) 2
  simp [e02] at e1 e2
  have hsq : a ^ 2 = w ^ 2 := by
    rw [← e1, one_mul] at e2
    field_simp at e2
    linear_combination -e2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hwa | hwa
  · left
    subst hwa
    intro g
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [slConj_scalar_diag A a a ha hw hA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp
  · right
    have hwa' : w = -a := by linear_combination hwa
    subst hwa'
    intro g
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [slConj_scalar_diag A a (-a) ha hw hA, coe_xN_conj]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> field_simp

theorem inv_matrix_block (A : GL (Fin 3) F) (u w : F) (hu : u ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w]) :
    ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by
  have h2 : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h0 : (!![0, u, 0; -u, 0, 0; 0, 0, w] : Matrix (Fin 3) (Fin 3) F) *
      !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hu, hw]
  calc ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      = ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) *
        !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by
        rw [hA, Matrix.mul_assoc, h0, Matrix.mul_one]
    _ = !![0, -u⁻¹, 0; u⁻¹, 0, 0; 0, 0, w⁻¹] := by rw [h2, Matrix.one_mul]

theorem slConj_e02_inv_transpose (A : GL (Fin 3) F) (u w : F) (hu : u ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w]) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      ((e02 1)⁻¹ : SL(3, F)).transpose = e21 (w * u⁻¹) := by
  apply Subtype.ext
  rw [coe_slConj, coe_inv_transpose_e02, inv_matrix_block A u w hu hw hA, hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [e21] <;> field_simp

theorem slConj_e21_inv_transpose (A : GL (Fin 3) F) (u w : F) (hu : u ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w]) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
      ((e21 (w * u⁻¹))⁻¹ : SL(3, F)).transpose = e02 (-1) := by
  apply Subtype.ext
  rw [coe_slConj, coe_inv_transpose_e21, inv_matrix_block A u w hu hw hA, hA]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp [e02] <;> field_simp

theorem fin1 (h2 : (2 : F) ≠ 0) (A : GL (Fin 3) F) (u w : F) (hu : u ≠ 0) (hw : w ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) F) = !![0, u, 0; -u, 0, 0; 0, 0, w])
    (hα : (conjAut 3 F A * dualAut 3 F) * (conjAut 3 F A * dualAut 3 F) = 1) : False := by
  have h := congrArg (fun φ : MulAut (projectiveSL 3 F) => φ (proj 3 F (e02 1))) hα
  simp only [MulAut.mul_apply, MulAut.one_apply, dualAut_proj, conjAut_proj] at h
  rw [slConj_e02_inv_transpose A u w hu hw hA, slConj_e21_inv_transpose A u w hu hw hA] at h
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists h
  have e1 := congrFun (congrFun hcm 0) 0
  have e2 := congrFun (congrFun hcm 0) 2
  simp [e02] at e1 e2
  rw [← e1] at e2
  apply h2
  linear_combination e2

theorem psl3_aut_centralizing [Finite F] (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 3 F))
    (hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), α (proj 3 F r) = proj 3 F r)
    (hα : α * α = 1) :
    (∀ g : SL(3, F), α (proj 3 F g) = proj 3 F g) ∨
      (∀ g : SL(3, F), α (proj 3 F g) = proj 3 F (xN * g * xN⁻¹)) := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, w, ha, hw, hA⟩ := case0 h2 A σ hfix
    subst hσ
    have h1 : fieldAut 3 F (RingEquiv.refl F) = 1 := map_one (fieldAut 3 F)
    rw [h1, mul_one] at hα ⊢
    exact fin0 A a w ha hw hA hα
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, u, w, hu, hw, hA⟩ := case1 h2 A σ hfix
    subst hσ
    have h1 : fieldAut 3 F (RingEquiv.refl F) = 1 := map_one (fieldAut 3 F)
    rw [h1, mul_one] at hα
    exact (fin1 h2 A u w hu hw hA hα).elim

end ChainL

end CFSG.ClassicalInvolution.ModelFacts.Orth15
