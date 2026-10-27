module

public import CFSG.GH74.GLS.Stage2.Final.ModelRefl

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

variable {F : Type} [Field F]

theorem e4s0 : e4.symm (0 : Fin 4) = Sum.inl 0 := rfl
theorem e4s1 : e4.symm (1 : Fin 4) = Sum.inl 1 := rfl
theorem e4s2 : e4.symm (2 : Fin 4) = Sum.inr 0 := rfl
theorem e4s3 : e4.symm (3 : Fin 4) = Sum.inr 1 := rfl

theorem blk4_entry' (X Y : Matrix (Fin 2) (Fin 2) F) (a b : Fin 4) :
    blk4 X Y a b = fromBlocks X 0 0 Y (e4.symm a) (e4.symm b) := rfl

@[expose] def permS (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨!![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1], !![1, 0, 0, 0; 0, 0, 1, 0; 0, -1, 0, 0; 0, 0, 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]⟩

theorem coe_permS : ((permS F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
    !![1, 0, 0, 0; 0, 0, -1, 0; 0, 1, 0, 0; 0, 0, 0, 1] := rfl

theorem det_permS : ((permS F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [coe_permS, Matrix.det_succ_row_zero, Fin.sum_univ_succ]

theorem permS_conj : permS F * diagGL (dRefl F) (dRefl F) * (permS F)⁻¹ = xyGL F := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, coe_permS, coe_diagGL, coe_dRefl, xyGL, blk4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, blk4_entry', e4s0, e4s1, e4s2, e4s3]

@[expose] def kronM (x : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![x 0 0, 0, x 0 1, 0; 0, x 0 0, 0, x 0 1; x 1 0, 0, x 1 1, 0; 0, x 1 0, 0, x 1 1]

theorem kronM_mul (x y : Matrix (Fin 2) (Fin 2) F) : kronM (x * y) = kronM x * kronM y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronM, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem kronM_one : kronM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kronM]

theorem det_kronM (x : Matrix (Fin 2) (Fin 2) F) : (kronM x).det = x.det ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [kronM, Matrix.det_fin_three, Fin.succAbove]
  rw [Matrix.det_fin_two]
  ring

@[expose] def kronGL (x : GL (Fin 2) F) : GL (Fin 4) F :=
  ⟨kronM (x : Matrix (Fin 2) (Fin 2) F), kronM ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
    by rw [← kronM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, kronM_one],
    by rw [← kronM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, kronM_one]⟩

theorem coe_kronGL (x : GL (Fin 2) F) :
    ((kronGL x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = kronM (x : Matrix (Fin 2) (Fin 2) F) := rfl

theorem kronGL_mul (x y : GL (Fin 2) F) : kronGL (x * y) = kronGL x * kronGL y := by
  apply Units.ext
  simp only [coe_kronGL, Units.val_mul, kronM_mul]

theorem kronGL_one : kronGL (1 : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp only [coe_kronGL, Units.val_one, kronM_one]

@[expose] def sig0 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

theorem coe_sig0 : ((sig0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl

theorem sig0_mul_self : sig0 F * sig0 F = 1 := by
  apply Units.ext
  simp [coe_sig0, Matrix.one_fin_two]

theorem kronGL_sig0 : kronGL (sig0 F) = swapGL F := by
  apply Units.ext
  rw [coe_kronGL, coe_sig0, coe_swapGL, wMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronM, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, e4s0, e4s1, e4s2, e4s3, Matrix.fromBlocks]


theorem kronGL_dRefl : kronGL (dRefl F) = xyGL F := by
  apply Units.ext
  rw [coe_kronGL, coe_dRefl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronM, xyGL, coe_diagGL, blk4_entry', e4s0, e4s1, e4s2, e4s3]

@[expose] def cmat (t : F) : Matrix (Fin 4) (Fin 4) F :=
  !![(t + 1) / 2, 0, (t - 1) / 2, 0; 0, 1, 0, 0; (t - 1) / 2, 0, (t + 1) / 2, 0; 0, 0, 0, 1]

theorem cmat_mul (h2 : (2 : F) ≠ 0) (s t : F) : cmat s * cmat t = cmat (s * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> ring

theorem cmat_one (h2 : (2 : F) ≠ 0) : cmat (1 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, one_add_one_eq_two, div_self h2]

theorem det_cmat (h2 : (2 : F) ≠ 0) (t : F) : (cmat t).det = t := by
  simp [cmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  field_simp
  ring

theorem cmat_swap (t : F) : cmat t * (wMat : Matrix (Fin 4) (Fin 4) F) = wMat * cmat t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cmat, wMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, e4s0, e4s1, e4s2, e4s3, Matrix.fromBlocks]

theorem conjTr_cmat (σ : F ≃+* F) (t : F) : conjTr σ (cmat t) = cmat (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, cmat, map_ofNat]


theorem permS_mem_uni {σ : F ≃+* F} : permS F ∈ uniGL σ 4 := by
  show conjTr σ ((permS F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
    ((permS F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, coe_permS, Matrix.mul_apply, Fin.sum_univ_four]

theorem conjTr_kronM (σ : F ≃+* F) (x : Matrix (Fin 2) (Fin 2) F) :
    conjTr σ (kronM x) = kronM (conjTr σ x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, kronM]

theorem kronGL_mem_uni {σ : F ≃+* F} {x : GL (Fin 2) F} (hx : x ∈ uniGL σ 2) :
    kronGL x ∈ uniGL σ 4 := by
  have hx' : conjTr σ (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = 1 := hx
  show conjTr σ (kronM (x : Matrix (Fin 2) (Fin 2) F)) * kronM (x : Matrix (Fin 2) (Fin 2) F) = 1
  rw [conjTr_kronM, ← kronM_mul, hx', kronM_one]

theorem sig0_mem_uni {σ : F ≃+* F} : sig0 F ∈ uniGL σ 2 := by
  show conjTr σ ((sig0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
    ((sig0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
  have h := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) (sig0_mul_self (F := F))
  simp only [Units.val_mul, Units.val_one] at h
  have hc : conjTr σ ((sig0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((sig0 F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [conjTr, coe_sig0]
  rw [hc]
  exact h

theorem norm_det_uni {σ : F ≃+* F} {a : GL (Fin 2) F} (ha : a ∈ uniGL σ 2) :
    σ (a : Matrix (Fin 2) (Fin 2) F).det * (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have ha' : conjTr σ (a : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) = 1 := ha
  have := congrArg Matrix.det ha'
  rw [Matrix.det_mul, Matrix.det_one] at this
  have h' : (conjTr σ (a : Matrix (Fin 2) (Fin 2) F)).det = σ (a : Matrix (Fin 2) (Fin 2) F).det := by
    simp only [conjTr, Matrix.det_transpose]
    exact (RingHom.map_det (σ : F →+* F) _).symm
  rwa [h'] at this

@[expose] def cGL (h2 : (2 : F) ≠ 0) (t : Fˣ) : GL (Fin 4) F :=
  ⟨cmat (t : F), cmat ((t⁻¹ : Fˣ) : F),
    by rw [cmat_mul h2, Units.mul_inv, cmat_one h2], by rw [cmat_mul h2, Units.inv_mul, cmat_one h2]⟩

theorem coe_cGL (h2 : (2 : F) ≠ 0) (t : Fˣ) :
    ((cGL h2 t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = cmat (t : F) := rfl

theorem cGL_comm_swap (h2 : (2 : F) ≠ 0) (t : Fˣ) : cGL h2 t * swapGL F = swapGL F * cGL h2 t := by
  apply Units.ext
  simp only [Units.val_mul, coe_cGL, coe_swapGL]
  exact cmat_swap _

theorem cGL_mem_uni (h2 : (2 : F) ≠ 0) {σ : F ≃+* F} {t : Fˣ} (ht : σ (t : F) * t = 1) :
    cGL h2 t ∈ uniGL σ 4 := by
  show conjTr σ (cmat (t : F)) * cmat (t : F) = 1
  rw [conjTr_cmat, cmat_mul h2, ht, cmat_one h2]

theorem diag_swap_conj (a : GL (Fin 2) F) :
    diagGL 1 a * swapGL F * (diagGL 1 a)⁻¹ = swapGL F * diagGL a a⁻¹ := by
  have h1 : swapGL F * diagGL a 1 * (swapGL F)⁻¹ = diagGL 1 a := swapGL_mul_diagGL_mul_inv a 1
  rw [mul_inv_eq_iff_eq_mul] at h1
  rw [diagGL_inv, ← h1, mul_assoc, diagGL_mul, inv_one, mul_one, one_mul]

theorem perm_conj_lin : ∃ k ∈ (ModelData.lin F).K4,
    k * diagGL (dRefl F) (dRefl F) * k⁻¹ = xyGL F :=
  ⟨permS F, ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, det_permS⟩, permS_conj⟩

theorem perm_conj_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) : ∃ k ∈ (ModelData.uni hF).K4,
    k * diagGL (dRefl F) (dRefl F) * k⁻¹ = xyGL F :=
  ⟨permS F, ((ModelData.uni hF).mem_K4 _).2 ⟨permS_mem_uni, det_permS⟩, permS_conj⟩

@[expose] def kronHom (F : Type) [Field F] : GL (Fin 2) F →* GL (Fin 4) F where
  toFun := kronGL
  map_one' := kronGL_one
  map_mul' := kronGL_mul

theorem sig0_ne_one : sig0 F ≠ 1 := by
  intro h
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_sig0] at this

theorem sig0_ne_neg_one : sig0 F ≠ -1 := by
  intro h
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [coe_sig0] at this

theorem kron_conj_of_refl {x : GL (Fin 2) F} (hx : x * sig0 F * x⁻¹ = dRefl F) :
    kronGL x * swapGL F * (kronGL x)⁻¹ = xyGL F := by
  have h := congrArg (kronHom F) hx
  rw [map_mul, map_mul, map_inv] at h
  have e1 : kronHom F (sig0 F) = swapGL F := kronGL_sig0
  have e2 : kronHom F (dRefl F) = xyGL F := kronGL_dRefl
  rw [e1, e2] at h
  exact h

theorem w_conj_lin (h2 : (2 : F) ≠ 0) : ∃ k ∈ (ModelData.lin F).K4,
    k * swapGL F * k⁻¹ = xyGL F := by
  obtain ⟨x, hxdet, hx⟩ := refl_conj_lin h2 sig0_mul_self sig0_ne_one sig0_ne_neg_one
  refine ⟨kronGL x, ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, ?_⟩, kron_conj_of_refl hx⟩
  rw [coe_kronGL, det_kronM, hxdet, one_pow]

theorem w_conj_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) : ∃ k ∈ (ModelData.uni hF).K4,
    k * swapGL F * k⁻¹ = xyGL F := by
  obtain ⟨x, hxU, hxdet, hx⟩ := refl_conj_uni hF hp2 sig0_mem_uni sig0_mul_self sig0_ne_one sig0_ne_neg_one
  refine ⟨kronGL x, ((ModelData.uni hF).mem_K4 _).2 ⟨kronGL_mem_uni hxU, ?_⟩, kron_conj_of_refl hx⟩
  rw [coe_kronGL, det_kronM, hxdet, one_pow]

theorem det_diag_cGL (h2 : (2 : F) ≠ 0) (a : GL (Fin 2) F) :
    ((diagGL 1 a * cGL h2 (Matrix.GeneralLinearGroup.det a)⁻¹ : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F).det = 1 := by
  have hd : ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = (a : Matrix (Fin 2) (Fin 2) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply a
  rw [Units.val_mul, Matrix.det_mul, det_diagGL, coe_cGL, det_cmat h2, Units.val_inv_eq_inv_val, hd]
  simp only [Units.val_one, Matrix.det_one, one_mul]
  exact mul_inv_cancel₀ (by rw [← hd]; exact (Matrix.GeneralLinearGroup.det a).ne_zero)

theorem ns_conj_core (h2 : (2 : F) ≠ 0) (a : GL (Fin 2) F) :
    (diagGL 1 a * cGL h2 (Matrix.GeneralLinearGroup.det a)⁻¹) * swapGL F *
      (diagGL 1 a * cGL h2 (Matrix.GeneralLinearGroup.det a)⁻¹)⁻¹ = swapGL F * diagGL a a⁻¹ := by
  set c := cGL h2 (Matrix.GeneralLinearGroup.det a)⁻¹ with hcdef
  have hc : c * swapGL F * c⁻¹ = swapGL F := by
    rw [hcdef, cGL_comm_swap h2, mul_assoc, mul_inv_cancel, mul_one]
  calc diagGL 1 a * c * swapGL F * (diagGL 1 a * c)⁻¹
      = diagGL 1 a * (c * swapGL F * c⁻¹) * (diagGL 1 a)⁻¹ := by group
    _ = swapGL F * diagGL a a⁻¹ := by rw [hc, diag_swap_conj]

theorem ns_conj_lin (h2 : (2 : F) ≠ 0) (a : GL (Fin 2) F) : ∃ k ∈ (ModelData.lin F).K4,
    k * swapGL F * k⁻¹ = swapGL F * diagGL a a⁻¹ :=
  ⟨_, ((ModelData.lin F).mem_K4 _).2 ⟨Subgroup.mem_top _, det_diag_cGL h2 a⟩, ns_conj_core h2 a⟩

theorem ns_conj_uni [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (a : GL (Fin 2) F)
    (ha : a ∈ (ModelData.uni hF).U2) : ∃ k ∈ (ModelData.uni hF).K4,
    k * swapGL F * k⁻¹ = swapGL F * diagGL a a⁻¹ := by
  have h2 : (2 : F) ≠ 0 := by
    have hF' : Nat.card F = p ^ (2 * f) := by rw [hF, ← pow_mul, mul_comm]
    exact CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow (Fact.out : p.Prime) hp2 hF'
  have hσ : ∀ x, unitaryInvolution F p f x = x ^ (p ^ f) := unitaryInvolution_apply F p f
  have hnorm := norm_det_uni (σ := unitaryInvolution F p f) ha
  have hd : ((Matrix.GeneralLinearGroup.det a : Fˣ) : F) = (a : Matrix (Fin 2) (Fin 2) F).det :=
    Matrix.GeneralLinearGroup.val_det_apply a
  have ht : unitaryInvolution F p f (((Matrix.GeneralLinearGroup.det a)⁻¹ : Fˣ) : F) *
      (((Matrix.GeneralLinearGroup.det a)⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hd, ← mul_inv, hnorm, inv_one]
  refine ⟨_, ((ModelData.uni hF).mem_K4 _).2 ⟨?_, det_diag_cGL h2 a⟩, ns_conj_core h2 a⟩
  refine Subgroup.mul_mem _ (((ModelData.uni hF).diag_mem_iff 1 a).2 ⟨Subgroup.one_mem _, ha⟩) ?_
  exact cGL_mem_uni h2 ht

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
