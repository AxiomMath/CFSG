module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.L32Tools
public import CFSG.RankThree.FFModules.ChiefFactors
public import CFSG.Quasithin.Background.L34OutFacts

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.DynkinA2

open Module Polynomial Matrix
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.RankThree.FFModules
open scoped MatrixGroups

private theorem x0Mat_mul_x0InvMat : x0Mat * x0InvMat = 1 := by decide

private theorem x0InvMat_mul_x0Mat : x0InvMat * x0Mat = 1 := by decide

private theorem det_x0Mat : x0Mat.det = 1 := by decide

private theorem det_x0InvMat : x0InvMat.det = 1 := by decide

private theorem x0Mat_cubic : x0Mat * x0Mat * x0Mat + x0Mat + 1 = 0 := by decide

private theorem x0InvMat_cubic :
    x0InvMat * x0InvMat * x0InvMat + x0InvMat + 1 = x0Mat := by decide

private theorem x0Mat_pow_seven : x0Mat ^ 7 = 1 := by decide

@[expose] def fMat {F : Type*} [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F :=
  M * M * M + M + 1

theorem fMat_conj {F : Type*} [Field F] {P Q : Matrix (Fin 3) (Fin 3) F}
    (M : Matrix (Fin 3) (Fin 3) F) (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    fMat (P * M * Q) = P * fMat M * Q := by
  unfold fMat
  have h : (P * M * Q) * (P * M * Q) * (P * M * Q) = P * (M * M * M) * Q := by
    calc (P * M * Q) * (P * M * Q) * (P * M * Q)
        = P * M * (Q * P) * M * (Q * P) * M * Q := by noncomm_ring
      _ = P * (M * M * M) * Q := by rw [hQP]; noncomm_ring
  rw [h]
  have h2 : P * (M * M * M + M + 1) * Q =
      P * (M * M * M) * Q + P * M * Q + P * Q := by noncomm_ring
  rw [h2, hPQ]

theorem fMat_transpose {F : Type*} [Field F] (M : Matrix (Fin 3) (Fin 3) F) :
    fMat Mᵀ = (fMat M)ᵀ := by
  simp [fMat, Matrix.transpose_mul, Matrix.transpose_add, Matrix.mul_assoc]

section Companion

variable (F : Type) [Field F] [CharP F 2]

@[expose] noncomputable def cMat : Matrix (Fin 3) (Fin 3) F :=
  x0Mat.map (ZMod.castHom (dvd_refl 2) F)

@[expose] noncomputable def dMat : Matrix (Fin 3) (Fin 3) F :=
  x0InvMat.map (ZMod.castHom (dvd_refl 2) F)

theorem cMat_mul_dMat : cMat F * dMat F = 1 := by
  rw [cMat, dMat, ← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F),
    x0Mat_mul_x0InvMat, Matrix.map_one _ (map_zero (ZMod.castHom (dvd_refl 2) F)) (map_one _)]

theorem dMat_mul_cMat : dMat F * cMat F = 1 := by
  rw [cMat, dMat, ← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F),
    x0InvMat_mul_x0Mat, Matrix.map_one _ (map_zero (ZMod.castHom (dvd_refl 2) F)) (map_one _)]

theorem det_cMat : (cMat F).det = 1 := by
  rw [cMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_x0Mat, map_one]

theorem det_dMat : (dMat F).det = 1 := by
  rw [dMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_x0InvMat, map_one]

theorem fMat_cMat : fMat (cMat F) = 0 := by
  unfold fMat
  rw [cMat]
  rw [← Matrix.map_one (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (map_zero (ZMod.castHom (dvd_refl 2) F)) (map_one _)]
  rw [← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F)]
  rw [← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F)]
  rw [← Matrix.map_add (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (hf := map_add _)]
  rw [← Matrix.map_add (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (hf := map_add _)]
  rw [x0Mat_cubic]
  exact Matrix.map_zero (ZMod.castHom (dvd_refl 2) F) (map_zero _)

theorem fMat_dMat : fMat (dMat F) = cMat F := by
  unfold fMat
  rw [dMat]
  rw [← Matrix.map_one (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (map_zero (ZMod.castHom (dvd_refl 2) F)) (map_one _)]
  rw [← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F)]
  rw [← Matrix.map_mul (f := ZMod.castHom (dvd_refl 2) F)]
  rw [← Matrix.map_add (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (hf := map_add _)]
  rw [← Matrix.map_add (f := ⇑(ZMod.castHom (dvd_refl 2) F)) (hf := map_add _)]
  rw [x0InvMat_cubic, cMat]

theorem cMat_pow_seven : cMat F ^ 7 = 1 := by
  rw [cMat, ← Matrix.map_pow x0Mat (ZMod.castHom (dvd_refl 2) F) 7,
    x0Mat_pow_seven, Matrix.map_one _ (map_zero (ZMod.castHom (dvd_refl 2) F)) (map_one _)]

theorem map_cMat (σ : F ≃+* F) : (cMat F).map σ = cMat F := by
  ext i j
  rw [cMat, Matrix.map_apply, Matrix.map_apply]
  exact DFunLike.congr_fun (RingHom.ext_zmod
    (σ.toRingHom.comp (ZMod.castHom (dvd_refl 2) F)) (ZMod.castHom (dvd_refl 2) F))
    (x0Mat i j)

theorem map_dMat (σ : F ≃+* F) : (dMat F).map σ = dMat F := by
  ext i j
  rw [dMat, Matrix.map_apply, Matrix.map_apply]
  exact DFunLike.congr_fun (RingHom.ext_zmod
    (σ.toRingHom.comp (ZMod.castHom (dvd_refl 2) F)) (ZMod.castHom (dvd_refl 2) F))
    (x0InvMat i j)

@[expose] noncomputable def cSL : SL(3, F) :=
  ⟨cMat F, det_cMat F⟩

@[expose] noncomputable def dSL : SL(3, F) :=
  ⟨dMat F, det_dMat F⟩

theorem cSL_inv : (cSL F)⁻¹ = dSL F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change cMat F * dMat F = 1
  exact cMat_mul_dMat F

theorem dSL_inv : (dSL F)⁻¹ = cSL F := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  change dMat F * cMat F = 1
  exact dMat_mul_cMat F

theorem cSL_pow_seven : cSL F ^ 7 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  exact cMat_pow_seven F

theorem fMat_cSL : fMat ((cSL F : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 0 := by
  change fMat (cMat F) = 0
  exact fMat_cMat F

theorem exists_mul_fMat_dualMat_cSL :
    ∃ N : Matrix (Fin 3) (Fin 3) F, N * fMat (dualMat (cSL F)) = 1 := by
  refine ⟨(dMat F)ᵀ, ?_⟩
  have h : dualMat (cSL F) = (dMat F)ᵀ := by
    rw [dualMat, cSL_inv]
    rfl
  rw [h, fMat_transpose, fMat_dMat, ← Matrix.transpose_mul, cMat_mul_dMat,
    Matrix.transpose_one]

theorem fMat_isGraphType_cSL {α : MulAut (SL(3, F))} (hα : CFSG.Quasithin.L34Out.IsGraphType α) :
    (∃ N : Matrix (Fin 3) (Fin 3) F,
      N * fMat ((α (cSL F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1) ∧
      fMat (dualMat (α (cSL F))) = 0 := by
  obtain ⟨A, σ, hA⟩ := hα.exists_matrix
  have hAinvA : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hAAinv : (A : Matrix (Fin 3) (Fin 3) F) *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((α (cSL F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (dMat F)ᵀ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hA, cSL_inv]
    change (A : Matrix (Fin 3) (Fin 3) F) * ((dMat F)ᵀ.map ⇑σ) *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (dMat F)ᵀ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.transpose_map, map_dMat F σ]
  have h2 : ((α (dSL F) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) * (cMat F)ᵀ *
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hA, dSL_inv]
    change (A : Matrix (Fin 3) (Fin 3) F) * ((cMat F)ᵀ.map ⇑σ) *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (A : Matrix (Fin 3) (Fin 3) F) * (cMat F)ᵀ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    rw [Matrix.transpose_map, map_cMat F σ]
  constructor
  · refine ⟨(A : Matrix (Fin 3) (Fin 3) F) * (dMat F)ᵀ *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), ?_⟩
    rw [h1, fMat_conj _ hAinvA hAAinv, fMat_transpose, fMat_dMat]
    calc (A * (dMat F)ᵀ * A⁻¹) * (A * (cMat F)ᵀ * A⁻¹)
        = A * (dMat F)ᵀ * (A⁻¹ * A) * (cMat F)ᵀ * A⁻¹ := by noncomm_ring
      _ = A * (dMat F)ᵀ * (cMat F)ᵀ * A⁻¹ := by rw [hAinvA]; noncomm_ring
      _ = A * ((cMat F * dMat F)ᵀ) * A⁻¹ := by
        have h : (dMat F)ᵀ * (cMat F)ᵀ = (cMat F * dMat F)ᵀ := by
          rw [← Matrix.transpose_mul]
        rw [show A * (dMat F)ᵀ * (cMat F)ᵀ * A⁻¹ =
          A * ((dMat F)ᵀ * (cMat F)ᵀ) * A⁻¹ by noncomm_ring, h]
      _ = 1 := by rw [cMat_mul_dMat, Matrix.transpose_one, mul_one, hAAinv]
  · have h3 : dualMat (α (cSL F)) =
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ * cMat F *
          (A : Matrix (Fin 3) (Fin 3) F)ᵀ := by
      rw [dualMat]
      have hinv : (α (cSL F))⁻¹ = α (dSL F) := by rw [← map_inv, cSL_inv]
      rw [hinv, h2, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, ← Matrix.mul_assoc]
    have hQP : (A : Matrix (Fin 3) (Fin 3) F)ᵀ *
        (((A⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAinvA, Matrix.transpose_one]
    have hPQ : (((A⁻¹ : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F)ᵀ *
        (A : Matrix (Fin 3) (Fin 3) F)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hAAinv, Matrix.transpose_one]
    rw [h3, fMat_conj (cMat F) hQP hPQ, fMat_cMat]
    simp

end Companion

section Intertwine

variable {Q : Type*} [AddCommGroup Q] [Module (ZMod 2) Q] {F : Type*} [Field F]

private theorem map_aeval_fL (T : Module.End (ZMod 2) Q) (φ : Q ≃+ (Fin 3 → F))
    {M : Matrix (Fin 3) (Fin 3) F} (hφ : ∀ v, φ (T v) = M *ᵥ φ v) (v : Q) :
    φ (aeval T fL v) = fMat M *ᵥ φ v := by
  rw [aeval_fL_apply, map_add, map_add, hφ, hφ, hφ]
  rw [fMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem ker_aeval_fL_eq_top_of_intertwine (T : Module.End (ZMod 2) Q) (φ : Q ≃+ (Fin 3 → F))
    {M : Matrix (Fin 3) (Fin 3) F} (hφ : ∀ v, φ (T v) = M *ᵥ φ v) (hM : fMat M = 0) :
    LinearMap.ker (aeval T fL) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [LinearMap.mem_ker]
  apply φ.injective
  rw [map_zero, map_aeval_fL T φ hφ v, hM, Matrix.zero_mulVec]

theorem ker_aeval_fL_eq_bot_of_intertwine (T : Module.End (ZMod 2) Q) (φ : Q ≃+ (Fin 3 → F))
    {M N : Matrix (Fin 3) (Fin 3) F} (hφ : ∀ v, φ (T v) = M *ᵥ φ v) (hN : N * fMat M = 1) :
    LinearMap.ker (aeval T fL) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  apply φ.injective
  rw [map_zero]
  have h0 : fMat M *ᵥ φ v = 0 := by
    rw [← map_aeval_fL T φ hφ v, hv, map_zero]
  calc φ v = (1 : Matrix (Fin 3) (Fin 3) F) *ᵥ φ v := (Matrix.one_mulVec _).symm
    _ = (N * fMat M) *ᵥ φ v := by rw [hN]
    _ = N *ᵥ (fMat M *ᵥ φ v) := (Matrix.mulVec_mulVec (φ v) N (fMat M)).symm
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

theorem ker_aeval_fL_one : LinearMap.ker (aeval (1 : Module.End (ZMod 2) Q) fL) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker, aeval_fL_apply] at hv
  simp only [Module.End.one_apply] at hv
  have h2 : v + v = 0 := by
    rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [h2] at hv
  simpa using hv

end Intertwine

section Factors

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) K V} {F : Type*} [Field F]
  {ψ : K ⧸ CFSG.pCore 2 K ≃* SL(3, F)} {U U' : Subrepresentation ρ}

theorem ker_aeval_fL_eq_top_of_natural (h : IsNaturalFactor ψ U U') {k : K}
    (hk : fMat ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 0) :
    LinearMap.ker (aeval (factorRep U U' k) fL) = ⊤ := by
  obtain ⟨φ, hφ⟩ := h
  exact ker_aeval_fL_eq_top_of_intertwine (factorRep U U' k) φ (hφ k) hk

theorem ker_aeval_fL_eq_bot_of_natural (h : IsNaturalFactor ψ U U') {k : K}
    {N : Matrix (Fin 3) (Fin 3) F}
    (hk : N * fMat ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1) :
    LinearMap.ker (aeval (factorRep U U' k) fL) = ⊥ := by
  obtain ⟨φ, hφ⟩ := h
  exact ker_aeval_fL_eq_bot_of_intertwine (factorRep U U' k) φ (hφ k) hk

theorem ker_aeval_fL_eq_top_of_dual (h : IsDualNaturalFactor ψ U U') {k : K}
    (hk : fMat (dualMat (ψ (k : K ⧸ CFSG.pCore 2 K))) = 0) :
    LinearMap.ker (aeval (factorRep U U' k) fL) = ⊤ := by
  obtain ⟨φ, hφ⟩ := h
  exact ker_aeval_fL_eq_top_of_intertwine (factorRep U U' k) φ (hφ k) hk

theorem ker_aeval_fL_eq_bot_of_dual (h : IsDualNaturalFactor ψ U U') {k : K}
    {N : Matrix (Fin 3) (Fin 3) F} (hk : N * fMat (dualMat (ψ (k : K ⧸ CFSG.pCore 2 K))) = 1) :
    LinearMap.ker (aeval (factorRep U U' k) fL) = ⊥ := by
  obtain ⟨φ, hφ⟩ := h
  exact ker_aeval_fL_eq_bot_of_intertwine (factorRep U U' k) φ (hφ k) hk

theorem isNaturalFactor_of_equiv {W W' : Subrepresentation ρ} (h : IsNaturalFactor ψ U U')
    (φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (W'.toSubmodule ⧸ factorSub W W'))
    (hφ : ∀ k x, φ (factorRep U U' k x) = factorRep W W' k (φ x)) :
    IsNaturalFactor ψ W W' := by
  obtain ⟨φ₀, hφ₀⟩ := h
  refine ⟨φ.symm.trans φ₀, fun k y => ?_⟩
  have h1 : factorRep U U' k (φ.symm y) = φ.symm (factorRep W W' k y) := by
    apply φ.injective
    rw [hφ]
    simp
  calc (φ.symm.trans φ₀) (factorRep W W' k y)
      = φ₀ (φ.symm (factorRep W W' k y)) := rfl
    _ = φ₀ (factorRep U U' k (φ.symm y)) := by rw [← h1]
    _ = ((ψ (k : K ⧸ CFSG.pCore 2 K) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          φ₀ (φ.symm y) := hφ₀ k (φ.symm y)

theorem isDualNaturalFactor_of_equiv {W W' : Subrepresentation ρ}
    (h : IsDualNaturalFactor ψ U U')
    (φ : (U'.toSubmodule ⧸ factorSub U U') ≃+ (W'.toSubmodule ⧸ factorSub W W'))
    (hφ : ∀ k x, φ (factorRep U U' k x) = factorRep W W' k (φ x)) :
    IsDualNaturalFactor ψ W W' := by
  obtain ⟨φ₀, hφ₀⟩ := h
  refine ⟨φ.symm.trans φ₀, fun k y => ?_⟩
  have h1 : factorRep U U' k (φ.symm y) = φ.symm (factorRep W W' k y) := by
    apply φ.injective
    rw [hφ]
    simp
  calc (φ.symm.trans φ₀) (factorRep W W' k y)
      = φ₀ (φ.symm (factorRep W W' k y)) := rfl
    _ = φ₀ (factorRep U U' k (φ.symm y)) := by rw [← h1]
    _ = dualMat (ψ (k : K ⧸ CFSG.pCore 2 K)) *ᵥ φ₀ (φ.symm y) := hφ₀ k (φ.symm y)

theorem finrank_pos_of_natural [Finite V] (h : IsNaturalFactor ψ U U') :
    0 < finrank (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') := by
  obtain ⟨φ, -⟩ := h
  have : Finite (U'.toSubmodule ⧸ factorSub U U') := factor_finite U U'
  have : Module.Finite (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') :=
    Module.Finite.of_finite
  have : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := φ.toEquiv.nontrivial
  exact Module.finrank_pos

theorem finrank_pos_of_dual [Finite V] (h : IsDualNaturalFactor ψ U U') :
    0 < finrank (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') := by
  obtain ⟨φ, -⟩ := h
  have : Finite (U'.toSubmodule ⧸ factorSub U U') := factor_finite U U'
  have : Module.Finite (ZMod 2) (U'.toSubmodule ⧸ factorSub U U') :=
    Module.Finite.of_finite
  have : Nontrivial (U'.toSubmodule ⧸ factorSub U U') := φ.toEquiv.nontrivial
  exact Module.finrank_pos

end Factors

end CFSG.LocalAnalysis.RankThreeUC.S15.DynkinA2

end
