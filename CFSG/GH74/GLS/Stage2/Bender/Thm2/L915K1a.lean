module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCModel

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix Subgroup CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
open scoped MatrixGroups

section Elements

variable {F : Type} [Field F]

@[expose] def k1_xU (t : F) : SL(3, F) :=
  ⟨!![1, t, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def k1_xL (t : F) : SL(3, F) :=
  ⟨!![1, 0, 0; t, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

@[expose] def k1_dg : SL(3, F) :=
  ⟨!![-1, 0, 0; 0, 1, 0; 0, 0, -1], by simp [Matrix.det_fin_three]⟩

theorem k1_coe_xU (t : F) :
    ((k1_xU t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, t, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem k1_coe_xL (t : F) :
    ((k1_xL t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; t, 1, 0; 0, 0, 1] := rfl

theorem k1_coe_dg :
    ((k1_dg : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := rfl

theorem k1_xU_zero : (k1_xU 0 : SL(3, F)) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xU]

theorem k1_xL_zero : (k1_xL 0 : SL(3, F)) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xL]

theorem k1_xU_mul (s t : F) : k1_xU s * k1_xU t = k1_xU (s + t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xU, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem k1_xL_mul (s t : F) : k1_xL s * k1_xL t = k1_xL (s + t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xL, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem k1_xU_pow (t : F) (k : ℕ) : (k1_xU t : SL(3, F)) ^ k = k1_xU (k • t) := by
  induction k with
  | zero => simp [k1_xU_zero]
  | succ k ih => rw [pow_succ, ih, k1_xU_mul]; simp [add_smul]

theorem k1_xL_pow (t : F) (k : ℕ) : (k1_xL t : SL(3, F)) ^ k = k1_xL (k • t) := by
  induction k with
  | zero => simp [k1_xL_zero]
  | succ k ih => rw [pow_succ, ih, k1_xL_mul]; simp [add_smul]

theorem k1_xU_pow_char {p : ℕ} [CharP F p] (t : F) : (k1_xU t : SL(3, F)) ^ p = 1 := by
  rw [k1_xU_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, k1_xU_zero]

theorem k1_xL_pow_char {p : ℕ} [CharP F p] (t : F) : (k1_xL t : SL(3, F)) ^ p = 1 := by
  rw [k1_xL_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, k1_xL_zero]

theorem k1_inv_xU (t : F) : (k1_xU t : SL(3, F))⁻¹ = k1_xU (-t) := by
  rw [inv_eq_iff_mul_eq_one, k1_xU_mul]
  simp [k1_xU_zero]

theorem k1_inv_xL (t : F) : (k1_xL t : SL(3, F))⁻¹ = k1_xL (-t) := by
  rw [inv_eq_iff_mul_eq_one, k1_xL_mul]
  simp [k1_xL_zero]

theorem k1_transpose_xU (t : F) : (k1_xU t : SL(3, F)).transpose = k1_xL t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xU, k1_coe_xL, SpecialLinearGroup.coe_transpose]

theorem k1_transpose_xL (t : F) : (k1_xL t : SL(3, F)).transpose = k1_xU t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xU, k1_coe_xL, SpecialLinearGroup.coe_transpose]

theorem k1_map_xU (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (k1_xU t) = k1_xU (σ t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xU, SpecialLinearGroup.map_apply_coe]

theorem k1_map_xL (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (k1_xL t) = k1_xL (σ t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_xL, SpecialLinearGroup.map_apply_coe]

theorem k1_map_dg (σ : F ≃+* F) :
    SpecialLinearGroup.map σ.toRingHom (k1_dg : SL(3, F)) = k1_dg := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_dg, SpecialLinearGroup.map_apply_coe]

theorem k1_xU_mem_CenD (t : F) : k1_xU t ∈ CenD F := by
  rw [mem_CenD]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k1_coe_xU, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem k1_xL_mem_CenD (t : F) : k1_xL t ∈ CenD F := by
  rw [mem_CenD]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k1_coe_xL, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem k1_dg_mem_CenD : (k1_dg : SL(3, F)) ∈ CenD F := by
  rw [mem_CenD]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [k1_coe_dg, coe_dNeg, Matrix.mul_apply, Fin.sum_univ_three]

theorem k1_dg_inv : (k1_dg : SL(3, F))⁻¹ = k1_dg := by
  rw [inv_eq_iff_mul_eq_one]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_dg, Matrix.mul_apply, Fin.sum_univ_three]

theorem k1_dg_transpose : (k1_dg : SL(3, F)).transpose = k1_dg := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k1_coe_dg, SpecialLinearGroup.coe_transpose]

end Elements

section Mat

variable {F : Type} [Field F]

theorem k1_graph_apply (g : SL(3, F)) :
    ((g⁻¹).transpose : SL(3, F)) =
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F g := rfl

theorem k1_mat0 [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (A : GL (Fin 3) F) (σ : F ≃+* F)
    {g : SL(3, F)} (hg : g ^ p = 1)
    (hfix : (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F g) = proj 3 F g) :
    (A : Matrix (Fin 3) (Fin 3) F) *
        ((SpecialLinearGroup.map σ.toRingHom g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [MulAut.mul_apply, fieldAut_proj, conjAut_proj] at hfix
  refine mul_eq_of_slConj_eq A ?_
  refine eq_of_proj_eq_of_pow_eq_one (p := p) ?_ hg hfix
  rw [← map_pow, ← map_pow, hg, map_one, map_one]

theorem k1_mat1 [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (A : GL (Fin 3) F) (σ : F ≃+* F)
    {g : SL(3, F)} (hg : g ^ p = 1)
    (hfix : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F g) = proj 3 F g) :
    (A : Matrix (Fin 3) (Fin 3) F) *
        ((SpecialLinearGroup.map σ.toRingHom ((g⁻¹).transpose) : SL(3, F)) :
          Matrix (Fin 3) (Fin 3) F) =
      (g : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj] at hfix
  refine mul_eq_of_slConj_eq A ?_
  refine eq_of_proj_eq_of_pow_eq_one (p := p) ?_ hg hfix
  rw [k1_graph_apply, ← map_pow, ← map_pow, ← map_pow, hg, map_one, map_one, map_one]

theorem k1_dual_map_xU (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (((k1_xU t : SL(3, F))⁻¹).transpose) = k1_xL (-σ t) := by
  rw [k1_inv_xU, k1_transpose_xU, k1_map_xL, map_neg]

theorem k1_dual_map_xL (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (((k1_xL t : SL(3, F))⁻¹).transpose) = k1_xU (-σ t) := by
  rw [k1_inv_xL, k1_transpose_xL, k1_map_xU, map_neg]

theorem k1_shape0 (M : Matrix (Fin 3) (Fin 3) F)
    (hU : M * ((k1_xU 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((k1_xU 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M)
    (hL : M * ((k1_xL 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((k1_xL 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) :
    M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 1 1 = M 0 0 := by
  have u00 := congrFun (congrFun hU 0) 0
  have u01 := congrFun (congrFun hU 0) 1
  have u02 := congrFun (congrFun hU 0) 2
  have u21 := congrFun (congrFun hU 2) 1
  have l00 := congrFun (congrFun hL 0) 0
  have l10 := congrFun (congrFun hL 1) 0
  have l20 := congrFun (congrFun hL 2) 0
  have l12 := congrFun (congrFun hL 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, k1_coe_xU, k1_coe_xL] at u00 u01 u02 u21 l00 l10 l20 l12
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination l00
  · linear_combination l12
  · linear_combination u00
  · linear_combination u02
  · linear_combination u21
  · linear_combination l20
  · linear_combination l10

theorem k1_shape1 (M : Matrix (Fin 3) (Fin 3) F)
    (hU : M * ((k1_xL (-1) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((k1_xU 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M)
    (hL : M * ((k1_xU (-1) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((k1_xL 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * M) :
    M 0 0 = 0 ∧ M 0 2 = 0 ∧ M 2 0 = 0 ∧ M 1 1 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0 ∧ M 1 0 = -M 0 1 := by
  have u00 := congrFun (congrFun hU 0) 0
  have u01 := congrFun (congrFun hU 0) 1
  have u02 := congrFun (congrFun hU 0) 2
  have u20 := congrFun (congrFun hU 2) 0
  have l01 := congrFun (congrFun hL 0) 1
  have l10 := congrFun (congrFun hL 1) 0
  have l12 := congrFun (congrFun hL 1) 2
  have l21 := congrFun (congrFun hL 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, k1_coe_xU, k1_coe_xL] at u00 u01 u02 u20 l01 l10 l12 l21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination l10
  · linear_combination l12
  · linear_combination l21
  · linear_combination u01
  · linear_combination u02
  · linear_combination u20
  · linear_combination -u00

end Mat

section Main

variable {F : Type} [Field F]

theorem k1_det_ne_zero (A : GL (Fin 3) F) : Matrix.det (A : Matrix (Fin 3) (Fin 3) F) ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

theorem k1_coprime_card_sub_one [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F) (k : ℕ) :
    Nat.Coprime (p ^ k) (Nat.card F - 1) := by
  refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hpF h
  rw [Nat.sub_sub_self hpos] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem k1_pow_card_sub_one [Finite F] (A : GL (Fin 3) F)
    (h01 : (A : Matrix (Fin 3) (Fin 3) F) 0 1 = 0) (h02 : (A : Matrix (Fin 3) (Fin 3) F) 0 2 = 0)
    (h10 : (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) (h12 : (A : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h20 : (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h21 : (A : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h11 : (A : Matrix (Fin 3) (Fin 3) F) 1 1 = (A : Matrix (Fin 3) (Fin 3) F) 0 0) :
    A ^ (Nat.card F - 1) = 1 := by
  have := Fintype.ofFinite F
  have hdet : Matrix.det (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 0 0 *
        (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [Matrix.det_fin_three]
    simp [h01, h02, h10, h12, h20, h21, h11]
  have hne := k1_det_ne_zero A
  rw [hdet] at hne
  have ha : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun h => hne (by simp [h])
  have hc : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := fun h => hne (by simp [h])
  have hA : (A : Matrix (Fin 3) (Fin 3) F) =
      Matrix.diagonal ![(A : Matrix (Fin 3) (Fin 3) F) 0 0, (A : Matrix (Fin 3) (Fin 3) F) 0 0,
        (A : Matrix (Fin 3) (Fin 3) F) 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21, h11]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hA, Matrix.diagonal_pow, Units.val_one, ← Matrix.diagonal_one,
    Nat.card_eq_fintype_card]
  congr 1
  funext i
  fin_cases i <;> simp [FiniteField.pow_card_sub_one_eq_one _ ha, FiniteField.pow_card_sub_one_eq_one _ hc]

theorem k1_eps0 [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (hpF : p ∣ Nat.card F)
    (A : GL (Fin 3) F) (σ : F ≃+* F) {k : ℕ} (hk : (conjAut 3 F A * fieldAut 3 F σ) ^ p ^ k = 1)
    (hU : ∀ t : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (k1_xU t)) = proj 3 F (k1_xU t))
    (hL : ∀ t : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (k1_xL t)) = proj 3 F (k1_xL t)) :
    conjAut 3 F A * fieldAut 3 F σ = 1 := by
  have hU' : ∀ t : F, (A : Matrix (Fin 3) (Fin 3) F) *
      ((k1_xU (σ t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((k1_xU t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro t
    have := k1_mat0 p A σ (k1_xU_pow_char t) (hU t)
    rwa [k1_map_xU] at this
  have hL' : ∀ t : F, (A : Matrix (Fin 3) (Fin 3) F) *
      ((k1_xL (σ t) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((k1_xL t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) := by
    intro t
    have := k1_mat0 p A σ (k1_xL_pow_char t) (hL t)
    rwa [k1_map_xL] at this
  have h1U := hU' 1
  have h1L := hL' 1
  rw [map_one] at h1U h1L
  obtain ⟨h01, h02, h10, h12, h20, h21, h11⟩ := k1_shape0 _ h1U h1L
  have hdet : Matrix.det (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 0 0 *
        (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [Matrix.det_fin_three]
    simp [h01, h02, h10, h12, h20, h21, h11]
  have hne := k1_det_ne_zero A
  rw [hdet] at hne
  have ha : (A : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := fun h => hne (by simp [h])
  have hσ : σ = 1 := by
    apply RingEquiv.ext
    intro t
    have e := congrFun (congrFun (hU' t) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, k1_coe_xU, h01, h11] at e
    have e' : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * σ t = (A : Matrix (Fin 3) (Fin 3) F) 0 0 * t := by
      linear_combination e
    exact mul_left_cancel₀ ha e'
  rw [hσ, map_one, mul_one] at hk ⊢
  have hpow : A ^ (Nat.card F - 1) = 1 := k1_pow_card_sub_one A h01 h02 h10 h12 h20 h21 h11
  have h1 : conjAut 3 F A ^ (Nat.card F - 1) = 1 := by rw [← map_pow, hpow, map_one]
  have h2 : orderOf (conjAut 3 F A) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)
        (k1_coprime_card_sub_one (Fact.out : p.Prime) hpF k))
      (orderOf_dvd_of_pow_eq_one h1)
  exact orderOf_eq_one_iff.mp h2

theorem k1_eps1_false [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hU : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (k1_xU 1)) =
      proj 3 F (k1_xU 1))
    (hL : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (k1_xL 1)) =
      proj 3 F (k1_xL 1))
    (hD : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F k1_dg) = proj 3 F k1_dg) :
    False := by
  have h1U := k1_mat1 p A σ (k1_xU_pow_char 1) hU
  have h1L := k1_mat1 p A σ (k1_xL_pow_char 1) hL
  rw [k1_dual_map_xU, map_one] at h1U
  rw [k1_dual_map_xL, map_one] at h1L
  obtain ⟨h00, h02, h20, h11, h12, h21, h10⟩ := k1_shape1 _ h1U h1L
  have hdet : Matrix.det (A : Matrix (Fin 3) (Fin 3) F) =
      (A : Matrix (Fin 3) (Fin 3) F) 0 1 * (A : Matrix (Fin 3) (Fin 3) F) 0 1 *
        (A : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    rw [Matrix.det_fin_three]
    simp [h00, h02, h20, h11, h12, h21, h10]
  have hne := k1_det_ne_zero A
  rw [hdet] at hne
  have ha : (A : Matrix (Fin 3) (Fin 3) F) 0 1 ≠ 0 := fun h => hne (by simp [h])
  have hc : (A : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := fun h => hne (by simp [h])
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj, conjAut_proj, k1_dg_inv,
    k1_dg_transpose, k1_map_dg] at hD
  have hs : (k1_dg : SL(3, F))⁻¹ *
      CatalogueBHigherLinearAction.slConjugation 3 F A k1_dg ∈ scalars 3 F :=
    proj_eq_proj_iff.mp hD.symm
  obtain ⟨c, -, hcs⟩ := mem_scalars.1 hs
  have key : CatalogueBHigherLinearAction.slConjugation 3 F A k1_dg =
      k1_dg * ((k1_dg : SL(3, F))⁻¹ *
        CatalogueBHigherLinearAction.slConjugation 3 F A k1_dg) := by group
  have hmat := mul_eq_of_slConj_eq A key
  rw [Matrix.SpecialLinearGroup.coe_mul, hcs] at hmat
  have e01 := congrFun (congrFun hmat 0) 1
  have e22 := congrFun (congrFun hmat 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, k1_coe_dg, Matrix.scalar_apply] at e01 e22
  have hc1 : (c : F) = 1 := by
    have : (A : Matrix (Fin 3) (Fin 3) F) 2 2 * ((c : F) - 1) = 0 := by linear_combination -e22
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  rw [hc1] at e01
  apply h2
  have : (A : Matrix (Fin 3) (Fin 3) F) 0 1 * 2 = 0 := by linear_combination e01
  exact (mul_eq_zero.mp this).resolve_left ha

theorem k1_aut_eq_one_of_fix_block [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (hpF : p ∣ Nat.card F) (α : MulAut (projectiveSL 3 F)) {k : ℕ} (hk : α ^ p ^ k = 1)
    (hU : ∀ t : F, α (proj 3 F (k1_xU t)) = proj 3 F (k1_xU t))
    (hL : ∀ t : F, α (proj 3 F (k1_xL t)) = proj 3 F (k1_xL t))
    (hD : α (proj 3 F k1_dg) = proj 3 F k1_dg) : α = 1 := by
  obtain ⟨A, σ, ε, hε, hα⟩ := (automorphism_generation (n := 3) (K := F) le_rfl).2 α
  interval_cases ε
  · rw [pow_zero, mul_one] at hα
    rw [hα] at hk hU hL ⊢
    exact k1_eps0 p hpF A σ hk hU hL
  · rw [pow_one] at hα
    exfalso
    rw [hα] at hU hL hD
    exact k1_eps1_false p h2 A σ (hU 1) (hL 1) hD

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
