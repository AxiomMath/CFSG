module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCClass

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

variable {K : Type} [Field K]

theorem conjAut_mem_range_of_sq (X : gsp 2 K) {l : K} (hl : l ^ 2 = (multiplierUnit X : K)) :
    conjAut 2 K X ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range := by
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hl
    exact (multiplierUnit X).ne_zero hl.symm
  set Xm := ((X : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
  have hμ : Xmᵀ * formJ 2 K * Xm = (multiplierUnit X : K) • formJ 2 K := multiplierUnit_spec X
  have hA'sp : (l⁻¹ • Xm)ᵀ * formJ 2 K * (l⁻¹ • Xm) = formJ 2 K := by
    rw [transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, hμ, smul_smul,
      smul_smul, ← hl]
    rw [show l⁻¹ * l⁻¹ * l ^ 2 = 1 by field_simp, one_smul]
  set A' : StatedSp 2 K := toSp (l⁻¹ • Xm) hA'sp with hA'def
  have hAz : (X : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (Units.mk0 l hl0) *
        (A' : GL (Fin 2 ⊕ Fin 2) K) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, hA'def, coe_toSp, Units.val_mk0,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  exact ⟨proj 2 K A', (conjAut_eq_conj_of_scalar_mul X _ A' hAz).symm⟩

theorem conjAut_mem_inn_sup [Finite K] (B : gsp 2 K)
    (hB : ∀ l : K, l ^ 2 ≠ (multiplierUnit B : K)) (X : gsp 2 K) :
    conjAut 2 K X ∈ (MulAut.conj : StatedProj (StatedSp 2 K) →* _).range ⊔
      zpowers (conjAut 2 K B) := by
  by_cases hX : ∃ l : K, l ^ 2 = (multiplierUnit X : K)
  · obtain ⟨l, hl⟩ := hX
    exact mem_sup_left (conjAut_mem_range_of_sq X hl)
  · push Not at hX
    classical
    have : Fintype K := Fintype.ofFinite K
    set Y : gsp 2 K := B⁻¹ * X with hY
    have hmY : (multiplierUnit Y : K) = (multiplierUnit B : K)⁻¹ * multiplierUnit X := by
      have h1 : multiplierUnit Y = multiplier 2 K Y := rfl
      rw [h1, hY, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      rfl
    have hsqB : ¬ IsSquare (multiplierUnit B : K) := by
      rintro ⟨r, hr⟩
      exact hB r (by rw [hr, sq])
    have hsqX : ¬ IsSquare (multiplierUnit X : K) := by
      rintro ⟨r, hr⟩
      exact hX r (by rw [hr, sq])
    have cB := quadraticChar_neg_one_iff_not_isSquare.mpr hsqB
    have cX := quadraticChar_neg_one_iff_not_isSquare.mpr hsqX
    have cBinv : quadraticChar K ((multiplierUnit B : K)⁻¹) = -1 := by
      have h1 : quadraticChar K ((multiplierUnit B : K)⁻¹) * quadraticChar K (multiplierUnit B) =
          1 := by
        rw [← map_mul, inv_mul_cancel₀ (multiplierUnit B).ne_zero, map_one]
      rw [cB] at h1
      linarith
    have cY : quadraticChar K ((multiplierUnit B : K)⁻¹ * multiplierUnit X) = 1 := by
      rw [map_mul, cBinv, cX]
      norm_num
    obtain ⟨r, hr⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero
      (inv_ne_zero (multiplierUnit B).ne_zero) (multiplierUnit X).ne_zero)).mp cY
    have hYin := conjAut_mem_range_of_sq Y (l := r) (by rw [hmY, hr, sq])
    have hXeq : X = B * Y := by rw [hY, mul_inv_cancel_left]
    rw [hXeq, map_mul]
    exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hYin)

variable (K) in
@[expose] def qJ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := kron 1 (1 + J₁)

theorem one_add_J₁_sq : (1 + J₁ : Matrix (Fin 2) (Fin 2) K) * (1 + J₁) = (2 : K) • J₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem one_add_J₁_transpose_mul :
    (1 + J₁ : Matrix (Fin 2) (Fin 2) K)ᵀ * (1 + J₁) = (2 : K) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J₁, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem one_add_J₁_comm : (1 + J₁ : Matrix (Fin 2) (Fin 2) K) * J₁ = J₁ * (1 + J₁) := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]

theorem qJ_symplectic : (qJ K)ᵀ * formJ 2 K * qJ K = (2 : K) • formJ 2 K := by
  rw [qJ, formJ_eq_kron, kron_transpose, transpose_one, kron_mul, kron_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  rw [one_add_J₁_transpose_mul, kron_smul_right']

theorem qJ_mul_qJ : qJ K * qJ K = (2 : K) • kron 1 J₁ := by
  rw [qJ, kron_mul, Matrix.one_mul, one_add_J₁_sq, kron_smul_right']

theorem isUnit_det_qJ (h2 : (2 : K) ≠ 0) : IsUnit (qJ K).det := by
  have h := congrArg Matrix.det (qJ_mul_qJ (K := K))
  rw [det_mul, det_smul, Fintype.card_sum, Fintype.card_fin] at h
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  have hd : (kron (1 : Matrix (Fin 2) (Fin 2) K) J₁).det ≠ 0 := by
    have := congrArg Matrix.det (T2_mul_T2 (K := K))
    rw [coe_T2, det_mul, det_neg, det_one, Fintype.card_sum, Fintype.card_fin] at this
    intro h1
    rw [h1, mul_zero] at this
    norm_num at this
  exact mul_ne_zero (pow_ne_zero _ h2) hd h.symm

@[expose] def qJgsp (h2 : (2 : K) ≠ 0) : gsp 2 K :=
  ⟨nonsingInvUnit (qJ K) (isUnit_det_qJ h2), ⟨Units.mk0 2 h2, by
    rw [Units.val_mk0]
    exact qJ_symplectic⟩⟩

theorem coe_qJgsp (h2 : (2 : K) ≠ 0) :
    (((qJgsp h2 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      qJ K := rfl

@[expose] def y2 (h2 : (2 : K) ≠ 0) : MulAut (StatedProj (StatedSp 2 K)) := conjAut 2 K (qJgsp h2)

theorem y2_proj (h2 : (2 : K) ≠ 0) {g : StatedSp 2 K}
    (hg : qJ K * ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * qJ K) :
    y2 h2 (proj 2 K g) = proj 2 K g := by
  rw [y2, conjAut_proj]
  congr 1
  apply sp_ext
  set A : GL (Fin 2 ⊕ Fin 2) K := ((qJgsp h2 : gsp 2 K) : GL (Fin 2 ⊕ Fin 2) K) with hAdef
  have hA : (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = qJ K := rfl
  rw [coe_conjSp, ← hAdef, Units.val_mul, Units.val_mul, hA, hg, Matrix.mul_assoc, ← hA,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem y2_u2 (h2 : (2 : K) ≠ 0) : y2 h2 (u2 K) = u2 K := by
  apply y2_proj h2
  rw [coe_T2, qJ, kron_mul, kron_mul]
  simp only [Matrix.mul_one]
  rw [one_add_J₁_comm]

theorem y2_Lsub (h2 : (2 : K) ≠ 0) {t : StatedProj (StatedSp 2 K)} (ht : t ∈ Lsub K) :
    y2 h2 t = t := by
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := ht
  apply y2_proj h2
  rw [coe_diagSL, qJ, kron_mul, kron_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul]

theorem y2_comm (h2 : (2 : K) ≠ 0) :
    y2 h2 * MulAut.conj (u2 K) = MulAut.conj (u2 K) * y2 h2 := by
  ext x
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, y2_u2 h2]

theorem y2_sq (h2 : (2 : K) ≠ 0) : y2 h2 * y2 h2 = MulAut.conj (u2 K) := by
  rw [y2, ← map_mul]
  apply conjAut_eq_conj_of_scalar_mul _ (Units.mk0 2 h2) (T2 K)
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_qJgsp, qJ_mul_qJ,
    GeneralLinearGroup.coe_scalar,
    Units.val_mk0, coe_T2, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul]

theorem y2_pow_four (h2 : (2 : K) ≠ 0) : y2 h2 ^ 4 = 1 := by
  have hu : u2 K * u2 K = 1 := by
    rw [u2, ← map_mul, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff]
    right
    rw [Subgroup.coe_mul, Units.val_mul]
    exact T2_mul_T2
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq (y2 h2), y2_sq, sq, ← map_mul, hu, map_one]

theorem u2_ne_one' : u2 K ≠ 1 := by
  intro h
  rw [u2, ← MonoidHom.mem_ker, ker_proj, mem_spScalars_iff, coe_T2] at h
  rcases h with h | h
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [kron, J₁] at this
  · have := congrFun (congrFun h (Sum.inl 0)) (Sum.inl 1)
    simp [kron, J₁] at this

theorem orderOf_y2 [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K)
    (hs : IsSimpleGroup (StatedProj (StatedSp 2 K))) : orderOf (y2 h2) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ¬ y2 h2 ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, y2_sq]
    intro h
    have hc : u2 K ∈ center (StatedProj (StatedSp 2 K)) := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 K)) => φ g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * u2 K = u2 K * g * (u2 K)⁻¹ * u2 K := by rw [this]
        _ = u2 K * g := by group
    exact u2_ne_one' (eq_one_of_mem_center_P h2 h4 hs hc)
  exact orderOf_eq_prime_pow hne (by rw [show 2 ^ (1 + 1) = 4 from rfl]; exact y2_pow_four h2)

end CFSG.ComponentClassification.CatFactsSp4
