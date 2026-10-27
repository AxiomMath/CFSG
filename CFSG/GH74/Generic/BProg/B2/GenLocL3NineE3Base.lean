module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3NineR3

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.CatalogueBHigherLinearAction Matrix GenLocL3Good GenLocL3Pair GenLocL3Seven
  GenLocL3Nine GenLocL3NineR3
open scoped MatrixGroups

namespace GenLocL3NineE3

variable {K : Type} [Field K]

theorem inv_transpose_transvection (t : K) :
    ((Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) t)⁻¹).transpose =
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.adjugate_fin_three, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.add_apply]

theorem conj_map_transvection [Finite K] (u : Fin 3 → Kˣ) (σ : K ≃+* K) :
    slConjugation 3 K (diag3 u) (Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K))) =
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide)
        ((u 0 : K) * ((u 1)⁻¹ : Kˣ)) := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    CFSG.LinearGroups.coe_transvection, coe_diag3, coe_diag3_inv, CFSG.LinearGroups.coe_transvection]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.add_apply, Matrix.one_apply]

theorem dualAut_not_mem_noDual [Finite K] : LinearFlag.dualAut 3 K ∉ noDual K := by
  rintro ⟨x, σ, hx, h⟩
  obtain ⟨u, rfl⟩ := exists_diag3 hx
  have h1 := congrArg (fun φ : MulAut (LinearFlag.projectiveSL 3 K) => φ (LinearFlag.proj 3 K
    (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K)))) h
  simp only [MulAut.mul_apply] at h1
  rw [LinearFlag.dualAut_proj, LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj, inv_transpose_transvection,
    conj_map_transvection, LinearFlag.proj_eq_proj_iff] at h1
  obtain ⟨c, -, hc⟩ := h1
  have e := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hc
  have e1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 1 0) hc
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    CFSG.LinearGroups.coe_transvection, Matrix.adjugate_fin_three, Matrix.mul_apply, Matrix.add_apply,
    Fin.sum_univ_three] at e e1


theorem slConj_diag2_slFieldAut_anti [Finite K] (a b : Kˣ) {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3)
    {β : K} (hβ : β ≠ 0) (hrel : β * β * (a : K) = (b : K)) :
    slConjugation 2 K (diag2 a b) (GLS.IVK.Lifted.slFieldAut σ (anti hβ)) = anti hβ := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, GLS.IVK.Lifted.slFieldAut_apply,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_diag2, coe_diag2_inv]
  have hb : (b : K) ≠ 0 := b.ne_zero
  have ha : (a : K) ≠ 0 := a.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [anti, Matrix.mul_apply, Matrix.diagonal_apply, Units.val_inv_eq_inv_val, hσ, Matrix.map_apply]
  · field_simp
    linear_combination hrel
  · field_simp
    linear_combination hrel


theorem fixed_anti_of_field [Finite K] (m : Fin 3) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy : y ∈ frameStab 3 K) {u : Fin 3 → Kˣ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0)
    {β : K} (hβ : β ≠ 0) (hrel : β * β * (u (crd m 0) : K) = (u (crd m 1) : K)) :
    y (phiM m (anti hβ)) = phiM m (anti hβ) := by
  have h1 := restM_spec m ⟨y, hy⟩ (anti hβ)
  rw [rho_data m hy (Nat.zero_le 1) h, pow_zero, mul_one] at h1
  rw [show (⟨y, hy⟩ : frameStab 3 K).1 = y from rfl] at h1
  rw [h1, MulAut.mul_apply, slConj_diag2_slFieldAut_anti _ _ hσ hβ hrel]

theorem sigma_eq_pow [Finite K] (hK : Nat.card K = 9) {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    ∀ x, σ x = x ^ 3 := by
  have hK' : Nat.card K = 3 ^ 2 := by simpa using hK
  intro x
  have := (LinearFlag.even_and_eq_pow_of_involution_prime Nat.prime_three (by norm_num) hK' hσ hσσ).2 x
  simpa using this


theorem coe_map_diag3 (σ : K ≃+* K) (u : Fin 3 → Kˣ) :
    ((GeneralLinearGroup.map (σ : K →+* K) (diag3 u) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun a => σ (u a : K) := by
  show RingHom.mapMatrix (σ : K →+* K) ((diag3 u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
  rw [coe_diag3]
  ext i j
  by_cases h : i = j <;> simp [h, RingHom.mapMatrix_apply]

theorem quartic_equal [Finite K] (hK : Nat.card K = 9) {y : MulAut (LinearFlag.projectiveSL 3 K)}
    (hy2 : y * y = 1) {u : Fin 3 → Kˣ} {σ : K ≃+* K} (hσ1 : σ ≠ 1)
    (h : y = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0) :
    ∀ i i', ((u i : Kˣ) : K) ^ 4 = (u i' : K) ^ 4 := by
  have hσσ : σ * σ = 1 := sigma_sq_one_of_involution hy2 (Nat.zero_le 1) h
  have hpow := sigma_eq_pow hK hσ1 hσσ
  rw [h, pow_zero, mul_one, LinearFlag.conjAut_mul_fieldAut_mul, hσσ, map_one, mul_one] at hy2
  obtain ⟨c, hc0, hc⟩ := GenLocL3NFAux.scalar_of_conjAut_eq (diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 u))
    1 (by rw [hy2, map_one])
  have hd : ∀ j, c * ((u j : K) ^ 4) = 1 := by
    intro j
    have := congrFun (congrFun hc j) j
    simp only [Units.val_one, Matrix.one_apply_eq, Units.val_mul, coe_diag3, coe_map_diag3,
      Matrix.diagonal_mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul, hpow] at this
    linear_combination -this
  intro i i'
  have : c * ((u i : K) ^ 4) = c * ((u i' : K) ^ 4) := by rw [hd i, hd i']
  exact mul_left_cancel₀ hc0 this


theorem coe_inverseTranspose_diag3 (u : Fin 3 → Kˣ) :
    ((GeneralLinearGroup.inverseTranspose (diag3 u) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun a => (((u a)⁻¹ : Kˣ) : K) := by
  rw [GeneralLinearGroup.coe_inverseTranspose, coe_diag3_inv, Matrix.diagonal_transpose]

theorem comm_relation [Finite K] {ya yr : MulAut (LinearFlag.projectiveSL 3 K)}
    (hcomm : ya * yr = yr * ya) {u v : Fin 3 → Kˣ} {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3)
    (ha : ya = LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K ^ 0)
    (hr : yr = LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.fieldAut 3 K 1 * LinearFlag.dualAut 3 K ^ 1) :
    ∀ i i', (((u i : Kˣ) : K) * (v i : K)) ^ 2 = (((u i' : Kˣ) : K) * (v i' : K)) ^ 2 := by
  have s1 := LinearFlag.fieldAut_mul_conjAut (n := 3) (K := K) σ (diag3 v)
  have s2 := LinearFlag.dualAut_mul_conjAut (n := 3) (K := K) (diag3 u)
  have s3 := LinearFlag.dualAut_mul_fieldAut (n := 3) (K := K) σ
  have e1 : ya * yr = LinearFlag.conjAut 3 K (diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 v)) *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K := by
    rw [ha, hr, pow_zero, pow_one, mul_one, map_one, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ *
          (LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K)
        = LinearFlag.conjAut 3 K (diag3 u) * (LinearFlag.fieldAut 3 K σ *
          LinearFlag.conjAut 3 K (diag3 v)) * LinearFlag.dualAut 3 K := by simp only [mul_assoc]
      _ = _ := by rw [s1]; simp only [mul_assoc]
  have e2 : yr * ya = LinearFlag.conjAut 3 K (diag3 v * GeneralLinearGroup.inverseTranspose (diag3 u)) *
      LinearFlag.fieldAut 3 K σ * LinearFlag.dualAut 3 K := by
    rw [ha, hr, pow_zero, pow_one, mul_one, map_one, mul_one, map_mul]
    calc LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.dualAut 3 K *
          (LinearFlag.conjAut 3 K (diag3 u) * LinearFlag.fieldAut 3 K σ)
        = LinearFlag.conjAut 3 K (diag3 v) * (LinearFlag.dualAut 3 K *
          LinearFlag.conjAut 3 K (diag3 u)) * LinearFlag.fieldAut 3 K σ := by simp only [mul_assoc]
      _ = LinearFlag.conjAut 3 K (diag3 v) * (LinearFlag.conjAut 3 K
          (GeneralLinearGroup.inverseTranspose (diag3 u)) * LinearFlag.dualAut 3 K) *
          LinearFlag.fieldAut 3 K σ := by rw [s2]
      _ = LinearFlag.conjAut 3 K (diag3 v) * LinearFlag.conjAut 3 K
          (GeneralLinearGroup.inverseTranspose (diag3 u)) * (LinearFlag.dualAut 3 K *
          LinearFlag.fieldAut 3 K σ) := by simp only [mul_assoc]
      _ = _ := by rw [s3]; simp only [mul_assoc]
  rw [e1, e2] at hcomm
  have hcomm' := mul_right_cancel (mul_right_cancel hcomm)
  have hcomm'' : LinearFlag.conjAut 3 K (diag3 u * GeneralLinearGroup.map (σ : K →+* K) (diag3 v)) =
      LinearFlag.conjAut 3 K (diag3 v * GeneralLinearGroup.inverseTranspose (diag3 u)) := by
    exact hcomm'
  obtain ⟨c, hc0, hc⟩ := GenLocL3NFAux.scalar_of_conjAut_eq _ _ hcomm''
  have hd : ∀ j, c * (((u j : Kˣ) : K) * (v j : K)) ^ 2 = 1 := by
    intro j
    have := congrFun (congrFun hc j) j
    simp only [Units.val_mul, coe_diag3, coe_map_diag3, coe_inverseTranspose_diag3,
      Matrix.diagonal_mul_diagonal, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul, hσ] at this
    have hu : ((u j : Kˣ) : K) ≠ 0 := (u j).ne_zero
    have hvj : ((v j : Kˣ) : K) ≠ 0 := (v j).ne_zero
    field_simp at this
    simp only [Units.val_inv_eq_inv_val] at this
    calc c * (((u j : Kˣ) : K) * (v j : K)) ^ 2 = ((v j : K) ^ 2 * c * (u j : K)) * (u j : K) := by ring
      _ = ((u j : Kˣ) : K)⁻¹ * (u j : K) := by rw [← this]
      _ = 1 := inv_mul_cancel₀ hu
  intro i i'
  have : c * (((u i : Kˣ) : K) * (v i : K)) ^ 2 = c * (((u i' : Kˣ) : K) * (v i' : K)) ^ 2 := by
    rw [hd i, hd i']
  exact mul_left_cancel₀ hc0 this


end GenLocL3NineE3

end CFSG.GH74.Generic.BProg.B2
