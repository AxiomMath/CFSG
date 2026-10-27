module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public section

namespace CFSG.GH74.Generic.S45

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CFSG.ComponentClassification.CatFactsSp4

variable {K : Type} [Field K]

@[expose] def sp4UHalf (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; -(2 : K)⁻¹, 0]

@[expose] def sp4WRot (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1, -1; 1, 1]

theorem sp4UHalf_det : (sp4UHalf K).det = (2 : K)⁻¹ := by
  simp [sp4UHalf, Matrix.det_fin_two_of]

theorem sp4WRot_transpose_mul : (sp4WRot K)ᵀ * sp4WRot K = (2 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4WRot, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sp4C2_symplectic (h2 : (2 : K) ≠ 0) :
    (kron (sp4UHalf K) (sp4WRot K))ᵀ * formJ 2 K * kron (sp4UHalf K) (sp4WRot K) = formJ 2 K := by
  rw [kron_symplectic_iff, sp4UHalf_det, sp4WRot_transpose_mul, smul_smul, inv_mul_cancel₀ h2, one_smul]

@[expose] noncomputable def sp4C2 (h2 : (2 : K) ≠ 0) : StatedSp 2 K := toSp (kron (sp4UHalf K) (sp4WRot K)) (sp4C2_symplectic h2)

theorem sp4C2_sq (h2 : (2 : K) ≠ 0) : sp4C2 h2 * sp4C2 h2 = T2 K := by
  apply sp_ext
  simp only [Subgroup.coe_mul, Units.val_mul, sp4C2, coe_toSp, coe_T2, kron_mul]
  have hu : sp4UHalf K * sp4UHalf K = (-(2 : K)⁻¹) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sp4UHalf, Matrix.mul_apply, Fin.sum_univ_two]
  have hw : sp4WRot K * sp4WRot K = (-2 : K) • (J₁ : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sp4WRot, J₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  rw [hu, hw, kron_smul_left, smul_smul]
  have : (-(2 : K)⁻¹) * (-2) = 1 := by field_simp
  rw [this, one_smul]

@[expose] def sp4KRot (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![1, 1; -1, 1]

theorem sp4KRot_det : (sp4KRot K).det = (2 : K) := by
  simp [sp4KRot, Matrix.det_fin_two_of]
  norm_num

theorem sp4KRot_sq : sp4KRot K * sp4KRot K = (2 : K) • (J₁ : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4KRot, J₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

variable {a y : K}

@[expose] def sp4XI (K : Type) [Field K] (a y : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  kron (sp4KRot K) (y • sA a)

theorem sp4XI_twisted (hy : 2 * (y * y) * a = -1) :
    (sp4XI K a y)ᵀ * kron J₁ (dA a) * sp4XI K a y = kron J₁ (dA a) := by
  have h1 : (y • sA a)ᵀ * dA a * (y • sA a) = (y * y * (-a)) • dA a := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sA_transpose_dA_sA]
    rw [mul_assoc]
  have h2 : (sp4KRot K)ᵀ * J₁ * sp4KRot K = (2 : K) • (J₁ : Matrix (Fin 2) (Fin 2) K) := by
    rw [J₁, transpose_mul_J₁_mul, sp4KRot_det]
  have h3 : (2 : K) * (y * y * -a) = 1 := by linear_combination -hy
  rw [sp4XI, kron_transpose, kron_mul, kron_mul, h1, h2, kron_smul_left, smul_smul, h3, one_smul]

@[expose] noncomputable def sp4CI (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) : StatedSp 2 K :=
  toSp (bA a * sp4XI K a y * bAinv a) (bA_conj_symplectic ha (sp4XI_twisted hy))

theorem coe_cI (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) :
    (((sp4CI ha hy : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = bA a * sp4XI K a y * bAinv a := rfl

theorem aI_comm_cI (ha : a ≠ 0) :
    aI a * (bA a * sp4XI K a y * bAinv a) = (bA a * sp4XI K a y * bAinv a) * aI a := by
  have hk : kron 1 (sA a) * sp4XI K a y = sp4XI K a y * kron 1 (sA a) := by
    simp only [sp4XI, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
  calc aI a * (bA a * sp4XI K a y * bAinv a) =
      bA a * (kron 1 (sA a) * sp4XI K a y) * bAinv a := by
        simp only [aI, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]
    _ = (bA a * sp4XI K a y * bAinv a) * aI a := by
        rw [hk]
        simp only [aI, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]

theorem sp4XI_mul_self (hy : 2 * (y * y) * a = -1) :
    sp4XI K a y * sp4XI K a y = -kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 := by
  have hs : (y • sA a) * (y • sA a) = (y * y * a) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sA_mul_sA, zero_smul, add_zero, smul_smul]
  rw [sp4XI, kron_mul, sp4KRot_sq, hs, kron_smul_left, smul_smul]
  have h3 : (2 : K) * (y * y * a) = -1 := by linear_combination hy
  rw [h3, kron_smul_right', neg_one_smul]

theorem sp4CI_mul_self_coe (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) :
    ((((sp4CI ha hy * sp4CI ha hy : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -(bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_cI]
  calc bA a * sp4XI K a y * bAinv a * (bA a * sp4XI K a y * bAinv a) =
      bA a * (sp4XI K a y * sp4XI K a y) * bAinv a := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]
    _ = _ := by
        rw [sp4XI_mul_self hy, Matrix.mul_neg, Matrix.neg_mul]

theorem bA_kron_J₁_mul_self (ha : a ≠ 0) :
    (bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) *
      (bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) = -1 := by
  have hJ : (J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J₁, Matrix.mul_apply, Fin.sum_univ_two]
  calc (bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a) *
        (bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a)
      = bA a * (kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * kron J₁ 1) * bAinv a := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (bAinv a) (bA a), bAinv_mul_bA ha, Matrix.one_mul]
    _ = -1 := by
        rw [kron_mul, Matrix.mul_one, hJ, kron_neg_one_one, Matrix.mul_neg, Matrix.mul_one,
          Matrix.neg_mul, bA_mul_bAinv ha]

theorem bA_kron_J₁_ne_pm_one (ha : a ≠ 0) :
    ¬ (bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a = 1 ∨
      bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a = -1) := by
  set Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1
    with hYdef
  have hY : Y = bAinv a * (bA a * Y * bAinv a) * bA a := by
    calc Y = (bAinv a * bA a) * Y * (bAinv a * bA a) := by
          rw [bAinv_mul_bA ha, Matrix.one_mul, Matrix.mul_one]
      _ = bAinv a * (bA a * Y * bAinv a) * bA a := by simp only [Matrix.mul_assoc]
  have h00 : Y (Sum.inl 0) (Sum.inl 0) = 0 := by simp [hYdef, kron, J₁]
  rintro (hM | hM)
  · rw [hM, Matrix.mul_one, bAinv_mul_bA ha] at hY
    have := congrFun (congrFun hY (Sum.inl 0)) (Sum.inl 0)
    rw [h00] at this
    simp at this
  · rw [hM, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, bAinv_mul_bA ha] at hY
    have := congrFun (congrFun hY (Sum.inl 0)) (Sum.inl 0)
    rw [h00] at this
    simp at this

theorem sp4CI_pow_four_coe (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) :
    (((((sp4CI ha hy * sp4CI ha hy) * (sp4CI ha hy * sp4CI ha hy)) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = -1 := by
  rw [Subgroup.coe_mul, Units.val_mul, sp4CI_mul_self_coe ha hy, Matrix.neg_mul, Matrix.mul_neg,
    neg_neg]
  exact bA_kron_J₁_mul_self ha

theorem orderOf_proj_cI (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) :
    orderOf (proj 2 K (sp4CI ha hy)) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := proj 2 K (sp4CI ha hy))
    (by
      rw [pow_one, ← map_pow, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, pow_two,
        sp4CI_mul_self_coe ha hy]
      rintro (hcon | hcon)
      · exact bA_kron_J₁_ne_pm_one ha (Or.inr (neg_eq_iff_eq_neg.1 hcon))
      · exact bA_kron_J₁_ne_pm_one ha (Or.inl (neg_inj.1 hcon)))
    (by
      rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, ← MonoidHom.mem_ker, ker_proj,
        mem_spScalars_iff]
      right
      have : sp4CI ha hy ^ 4 = (sp4CI ha hy * sp4CI ha hy) * (sp4CI ha hy * sp4CI ha hy) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [this]
      exact sp4CI_pow_four_coe ha hy)
  rw [h]
  norm_num


theorem u2_ne_one_aux : u2 K ≠ 1 := by
  intro h
  rw [u2, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, coe_T2] at h
  rcases h with h | h
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [kron, J₁] at this
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [kron, J₁] at this

theorem exists_data_u2 (h2 : (2 : K) ≠ 0) {u g : StatedProj (StatedSp 2 K)}
    (hg : g⁻¹ * u * g = u2 K) :
    ∃ (A : gsp 2 K) (c : StatedSp 2 K), conjAut 2 K A = MulAut.conj u ∧ conjSp 2 K A c = c ∧
      orderOf (proj 2 K c) = 4 := by
  obtain ⟨g', rfl⟩ := proj_surjective g
  set A₀ : StatedSp 2 K := g' * T2 K * g'⁻¹ with hA₀
  have hu : u = proj 2 K A₀ := by
    have : u = proj 2 K g' * u2 K * (proj 2 K g')⁻¹ := by rw [← hg]; group
    rw [this, hA₀, u2]
    simp [map_mul, map_inv]
  let A : gsp 2 K := ⟨(A₀ : GL (Fin 2 ⊕ Fin 2) K), statedSp_le_gsp A₀.2⟩
  have hcA : conjAut 2 K A = MulAut.conj u := by
    rw [hu]
    exact conjAut_eq_conj_of_scalar_mul A 1 A₀ (by simp [A])
  have hc2 := sp4C2_sq h2
  refine ⟨A, g' * sp4C2 h2 * g'⁻¹, hcA, ?_, ?_⟩
  · have hconj : conjSp 2 K A (g' * sp4C2 h2 * g'⁻¹) = A₀ * (g' * sp4C2 h2 * g'⁻¹) * A₀⁻¹ :=
      Subtype.ext (by rw [coe_conjSp]; simp [A])
    rw [hconj, hA₀, ← hc2]
    group
  · have : proj 2 K (g' * sp4C2 h2 * g'⁻¹) = MulAut.conj (proj 2 K g') (proj 2 K (sp4C2 h2)) := by
      simp [map_mul, map_inv]
    rw [this, MulEquiv.orderOf_eq]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := proj 2 K (sp4C2 h2))
      (by
        rw [pow_one, ← map_pow, pow_two, hc2]
        exact u2_ne_one_aux)
      (by
        rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, ← MonoidHom.mem_ker, ker_proj,
          mem_spScalars_iff]
        right
        have : sp4C2 h2 ^ 4 = T2 K * T2 K := by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hc2]
        rw [this, Subgroup.coe_mul, Units.val_mul]
        exact T2_mul_T2)
    rw [h]
    norm_num

theorem exists_data_of_frame (ha : a ≠ 0) {A : gsp 2 K} {g : StatedSp 2 K}
    (hg : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a)
    {c₀ : StatedSp 2 K}
    (hcomm : ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * (c₀ : GL (Fin 2 ⊕ Fin 2) K) =
      (c₀ : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K))
    (hord : orderOf (proj 2 K c₀) = 4) :
    ∃ c : StatedSp 2 K, conjSp 2 K A c = c ∧ orderOf (proj 2 K c) = 4 := by
  have hGL : (A : GL (Fin 2 ⊕ Fin 2) K) * (g : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, coe_aIgsp]; exact hg)
  have hAeq : (A : GL (Fin 2 ⊕ Fin 2) K) =
      (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) *
        (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := by
    rw [← hGL]; group
  refine ⟨g * c₀ * g⁻¹, ?_, ?_⟩
  · apply Subtype.ext
    rw [coe_conjSp, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAeq]
    have hc' : ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) * (c₀ : GL (Fin 2 ⊕ Fin 2) K) *
        ((aIgsp ha : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K)⁻¹ = (c₀ : GL (Fin 2 ⊕ Fin 2) K) := by
      rw [mul_inv_eq_iff_eq_mul]; exact hcomm
    calc (g : GL (Fin 2 ⊕ Fin 2) K) * (aIgsp ha : GL (Fin 2 ⊕ Fin 2) K) *
          (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ *
          ((g : GL (Fin 2 ⊕ Fin 2) K) * (c₀ : GL (Fin 2 ⊕ Fin 2) K) *
            (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹) *
          ((g : GL (Fin 2 ⊕ Fin 2) K) * (aIgsp ha : GL (Fin 2 ⊕ Fin 2) K) *
            (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹)⁻¹
        = (g : GL (Fin 2 ⊕ Fin 2) K) * ((aIgsp ha : GL (Fin 2 ⊕ Fin 2) K) *
            (c₀ : GL (Fin 2 ⊕ Fin 2) K) * (aIgsp ha : GL (Fin 2 ⊕ Fin 2) K)⁻¹) *
          (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := by group
      _ = (g : GL (Fin 2 ⊕ Fin 2) K) * (c₀ : GL (Fin 2 ⊕ Fin 2) K) *
          (g : GL (Fin 2 ⊕ Fin 2) K)⁻¹ := by rw [hc']
  · have : proj 2 K (g * c₀ * g⁻¹) = MulAut.conj (proj 2 K g) (proj 2 K c₀) := by
      simp [map_mul, map_inv]
    rw [this, MulEquiv.orderOf_eq]
    exact hord

theorem exists_data_alphaI (ha : a ≠ 0) (hy : 2 * (y * y) * a = -1) {A : gsp 2 K} {g : StatedSp 2 K}
    (hg : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a) :
    ∃ c : StatedSp 2 K, conjSp 2 K A c = c ∧ orderOf (proj 2 K c) = 4 :=
  exists_data_of_frame ha hg
    (Units.ext (by rw [Units.val_mul, Units.val_mul, coe_aIgsp, coe_cI]; exact aI_comm_cI ha))
    (orderOf_proj_cI ha hy)

@[expose] def sp4KSL (h2 : (2 : K) ≠ 0) {s : K} (hs : s * s = 2) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨s⁻¹ • sp4KRot K, by
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact h2 (by rw [← hs]; ring)
    rw [Matrix.det_smul, sp4KRot_det, Fintype.card_fin]
    rw [← hs]
    field_simp⟩

theorem coe_sp4KSL (h2 : (2 : K) ≠ 0) {s : K} (hs : s * s = 2) :
    ((sp4KSL h2 hs : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      s⁻¹ • sp4KRot K := rfl

theorem sp4KSL_sq (h2 : (2 : K) ≠ 0) {s : K} (hs : s * s = 2) :
    ((sp4KSL h2 hs : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
      (sp4KSL h2 hs : Matrix.SpecialLinearGroup (Fin 2) K) = (J₁ : Matrix (Fin 2) (Fin 2) K) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact h2 (by rw [← hs]; ring)
  rw [coe_sp4KSL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sp4KRot_sq, smul_smul]
  have : s⁻¹ * s⁻¹ * 2 = 1 := by rw [← hs]; field_simp
  rw [this, one_smul]

theorem orderOf_proj_gI_sq (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) {s : K} (hs : s * s = 2) :
    orderOf (proj 2 K (gI ha (sp4KSL h2 hs))) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcoe : (((gI ha (sp4KSL h2 hs) * gI ha (sp4KSL h2 hs) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        bA a * kron (J₁ : Matrix (Fin 2) (Fin 2) K) 1 * bAinv a := by
    rw [← map_mul, coe_gI, Matrix.SpecialLinearGroup.coe_mul, sp4KSL_sq h2 hs]
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := proj 2 K (gI ha (sp4KSL h2 hs)))
    (by
      rw [pow_one, ← map_pow, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, pow_two, hcoe]
      exact bA_kron_J₁_ne_pm_one ha)
    (by
      rw [show 2 ^ (1 + 1) = 4 by norm_num, ← map_pow, ← MonoidHom.mem_ker, ker_proj,
        mem_spScalars_iff]
      right
      have h4 : gI ha (sp4KSL h2 hs) ^ 4 =
          (gI ha (sp4KSL h2 hs) * gI ha (sp4KSL h2 hs)) *
            (gI ha (sp4KSL h2 hs) * gI ha (sp4KSL h2 hs)) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
      rw [h4, Subgroup.coe_mul, Units.val_mul, hcoe]
      exact bA_kron_J₁_mul_self ha)
  rw [h]
  norm_num

theorem exists_data_alphaI_sq (h2 : (2 : K) ≠ 0) (ha : a ≠ 0) {s : K} (hs : s * s = 2)
    {A : gsp 2 K} {g : StatedSp 2 K}
    (hg : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * aI a) :
    ∃ c : StatedSp 2 K, conjSp 2 K A c = c ∧ orderOf (proj 2 K c) = 4 :=
  exists_data_of_frame ha hg (c₀ := gI ha (sp4KSL h2 hs))
    (Units.ext (by
      rw [Units.val_mul, Units.val_mul, coe_aIgsp, coe_gI]
      exact aI_comm_gI ha (sp4KSL h2 hs)))
    (orderOf_proj_gI_sq h2 ha hs)

end CFSG.GH74.Generic.S45
