module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLc
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CSLb

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OCL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag DiagL CSL

variable {F : Type} [Field F]

theorem uK_transpose (l c : F) : (uK l c 0)ᵀ = lK l c 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK, lK, Matrix.transpose_apply]

theorem wK_uK (l x : F) : (wK : Matrix (Fin 4) (Fin 4) F) * uK l x 0 = lK l (-x) 0 * wK := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK, lK, wK, Matrix.mul_apply, Fin.sum_univ_four]

theorem map_uK_zero (σ : F ≃+* F) (l x : F) : (uK l x 0).map σ = uK l (σ x) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK]

theorem sigma_eq_one_of_uK {l : F} {C : Matrix (Fin 4) (Fin 4) F} (hC : IsUnit C.det)
    (σ : F →+* F) (h : ∀ c, C * uK l (σ c) 0 = uK l c 0 * C) : ∀ c, σ c = c := by
  intro c
  by_contra hc
  have E : ∀ (d : F) (i j : Fin 4), (C * uK l (σ d) 0) i j = (uK l d 0 * C) i j :=
    fun d i j => by rw [h d]
  have hL : ∀ (d : F) (i : Fin 4), (C * uK l (σ d) 0) i 0 = C i 0 ∧
      (C * uK l (σ d) 0) i 1 = C i 1 ∧ (C * uK l (σ d) 0) i 2 = σ d * C i 0 + C i 2 ∧
      (C * uK l (σ d) 0) i 3 = σ d * C i 1 + C i 3 := by
    intro d i
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [uK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  have hR0 : ∀ (d : F) (j : Fin 4), (uK l d 0 * C) 0 j = C 0 j + d * C 2 j := by
    intro d j; simp [uK, Matrix.mul_apply, Fin.sum_univ_four]
  have hR1 : ∀ (d : F) (j : Fin 4), (uK l d 0 * C) 1 j = C 1 j + d * C 3 j := by
    intro d j; simp [uK, Matrix.mul_apply, Fin.sum_univ_four]
  have hsub : σ c - c ≠ 0 := sub_ne_zero.mpr hc
  have z20 : C 2 0 = 0 := by
    have e := E 1 0 0; rw [(hL 1 0).1, hR0] at e; linear_combination -e
  have z30 : C 3 0 = 0 := by
    have e := E 1 1 0; rw [(hL 1 1).1, hR1] at e; linear_combination -e
  have k02 := E 1 0 2
  rw [(hL 1 0).2.2.1, hR0, map_one] at k02
  have c02 := E c 0 2
  rw [(hL c 0).2.2.1, hR0] at c02
  have k12 := E 1 1 2
  rw [(hL 1 1).2.2.1, hR1, map_one] at k12
  have c12 := E c 1 2
  rw [(hL c 1).2.2.1, hR1] at c12
  have z00 : C 0 0 = 0 := by
    have : (σ c - c) * C 0 0 = 0 := by linear_combination c02 - c * k02
    exact (mul_eq_zero.1 this).resolve_left hsub
  have z10 : C 1 0 = 0 := by
    have : (σ c - c) * C 1 0 = 0 := by linear_combination c12 - c * k12
    exact (mul_eq_zero.1 this).resolve_left hsub
  have hcol : ∀ i, C i 0 = 0 := by
    intro i
    fin_cases i
    · exact z00
    · exact z10
    · exact z20
    · exact z30
  apply hC.ne_zero
  exact Matrix.det_eq_zero_of_column_eq_zero 0 hcol

@[expose] noncomputable def mZinv (l : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, l⁻¹, 0; 0, 0, 0, 1; -l⁻¹, 0, 0, 0; 0, -1, 0, 0]

theorem mZ_mul_mZinv {l : F} (hl : l ≠ 0) : mZ l * mZinv l = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mZ, mZinv, Matrix.mul_apply, Fin.sum_univ_four, hl]

theorem mZinv_mul_mZ {l : F} (hl : l ≠ 0) : mZinv l * mZ l = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mZ, mZinv, Matrix.mul_apply, Fin.sum_univ_four, hl]

theorem cancel_mZ' {l : F} (hl : l ≠ 0) {X Y : Matrix (Fin 4) (Fin 4) F}
    (h : X * mZ l = Y * mZ l) : X = Y := by
  have := congrArg (· * mZinv l) h
  simp only [Matrix.mul_assoc, mZ_mul_mZinv hl, Matrix.mul_one] at this
  exact this

theorem eq_of_mem_CA_dual_gen (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    (B : GL (Fin 4) F) (σ : F ≃+* F)
    (hg : conjAut 4 F B * fieldAut 4 F σ * dualAut 4 F ∈ CA F hl) :
    (∀ c, σ c = c) ∧ ∃ a b : F, (B : Matrix (Fin 4) (Fin 4) F) = eK l a b * mZ l := by
  have key : ∀ (u : SpecialLinearGroup (Fin 4) F) (M M' : Matrix (Fin 4) (Fin 4) F),
      proj 4 F u ∈ JK F hl → (u : Matrix (Fin 4) (Fin 4) F) = M →
      (((u⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) = M' →
      (M : Matrix (Fin 4) (Fin 4) F).trace = 4 → (M'.map σ).trace = 4 →
      (B : Matrix (Fin 4) (Fin 4) F) * (M'.map σ)ᵀ = M * B := by
    intro u M M' hu hM hM' htr htr'
    have hfix : (conjAut 4 F B * fieldAut 4 F σ) (proj 4 F (u⁻¹).transpose) = proj 4 F u := by
      have := hg _ hu
      rwa [MulAut.mul_apply, dualAut_proj] at this
    have e := mul_map_eq_of_map h4 B σ u (u⁻¹).transpose (by rw [hM]; exact htr)
      (by rw [Matrix.SpecialLinearGroup.coe_transpose, hM', Matrix.transpose_map,
        Matrix.trace_transpose]; exact htr') hfix
    rw [Matrix.SpecialLinearGroup.coe_transpose, hM', Matrix.transpose_map, hM] at e
    exact e
  have hdetB : IsUnit (B : Matrix (Fin 4) (Fin 4) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 B.isUnit
  have hσ : ∀ c, σ c = c := by
    have hU0 : ∀ c : F, (B : Matrix (Fin 4) (Fin 4) F) * (wK : Matrix (Fin 4) (Fin 4) F) *
        uK l (σ c) 0 = uK l c 0 * ((B : Matrix (Fin 4) (Fin 4) F) * wK) := by
      intro c
      have e := key (slUK l c 0) (uK l c 0) (uK l (-c) 0) ⟨_, slUK_mem_SK hl hl1 c 0, rfl⟩ rfl
        (by rw [coe_slUK_inv, neg_zero]) (trace_uK l c 0)
        (by have := trace_map_uK σ l (-c) (-0); rwa [neg_zero] at this)
      rw [map_uK_zero, map_neg, uK_transpose] at e
      rw [Matrix.mul_assoc, wK_uK, ← Matrix.mul_assoc, e, Matrix.mul_assoc]
    have hdet : IsUnit ((B : Matrix (Fin 4) (Fin 4) F) * wK).det := by
      rw [Matrix.det_mul, det_wK, mul_one]
      exact hdetB
    exact sigma_eq_one_of_uK hdet (σ : F →+* F) hU0
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map σ = M := fun M => by
    ext i j
    simp [hσ]
  set X := (B : Matrix (Fin 4) (Fin 4) F) * mZinv l with hX
  have hBX : (B : Matrix (Fin 4) (Fin 4) F) = X * mZ l := by
    rw [hX, Matrix.mul_assoc, mZinv_mul_mZ hl, Matrix.mul_one]
  have hUX : ∀ a b : F, X * uK l a b = uK l a b * X := by
    intro a b
    have e := key (slUK l a b) (uK l a b) (uK l (-a) (-b)) ⟨_, slUK_mem_SK hl hl1 a b, rfl⟩ rfl
      (coe_slUK_inv l a b) (trace_uK l a b) (trace_map_uK σ l (-a) (-b))
    rw [hmap, hBX, Matrix.mul_assoc, mZ_uK, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at e
    exact cancel_mZ' hl e
  have hLX : ∀ a b : F, X * lK l a b = lK l a b * X := by
    intro a b
    have e := key (slLK l a b) (lK l a b) (lK l (-a) (-b)) ⟨_, slLK_mem_SK hl hl1 a b, rfl⟩ rfl
      (coe_slLK_inv l a b) (trace_lK l a b) (trace_map_lK σ l (-a) (-b))
    rw [hmap, hBX, Matrix.mul_assoc, mZ_lK, ← Matrix.mul_assoc, ← Matrix.mul_assoc] at e
    exact cancel_mZ' hl e
  have hXeq := eq_of_comm_uK hl (hUX 1 0) (hLX 1 0) (hUX 0 1)
  refine ⟨hσ, X 0 0, X 1 0, ?_⟩
  rw [hBX, hXeq, smul_one_add_smul_kZero]
  congr 1

@[expose] def hT (l a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, -a, l * b; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem det_hT (l a b : F) : (hT l a b).det = 1 := by
  rw [hT, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem hT_form (l a b : F) : hT l a b * (eK l a b * mZ l) * (hT l a b)ᵀ = eK l a b * mZ l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hT, eK, mZ, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply] <;> ring

theorem hT_kZero_ne (h2 : (2 : F) ≠ 0) {l a b : F} (hab : a ≠ 0 ∨ b ≠ 0) (hl : l ≠ 0) :
    hT l a b * kZero l ≠ kZero l * hT l a b ∧ hT l a b * kZero l ≠ -(kZero l * hT l a b) := by
  have l12 : (hT l a b * kZero l) 1 2 = 0 := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  have r12 : (kZero l * hT l a b) 1 2 = -a := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  have l13 : (hT l a b * kZero l) 1 3 = 0 := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  have r13 : (kZero l * hT l a b) 1 3 = l * b := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  have l10 : (hT l a b * kZero l) 1 0 = 1 := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  have r10 : (kZero l * hT l a b) 1 0 = 1 := by
    simp [hT, kZero, Matrix.mul_apply, Fin.sum_univ_four]
  constructor
  · intro h
    have e2 := congrFun (congrFun h 1) 2
    have e3 := congrFun (congrFun h 1) 3
    rw [l12, r12] at e2
    rw [l13, r13] at e3
    rcases hab with ha | hb
    · exact ha (by linear_combination e2)
    · exact hb ((mul_eq_zero.1 e3.symm).resolve_left hl)
  · intro h
    have e := congrFun (congrFun h 1) 0
    rw [Matrix.neg_apply, l10, r10] at e
    exact h2 (by linear_combination e)

theorem conj_kZero_of_normalizes (h2 : (2 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    (hns : ¬ IsSquare l) {H : SpecialLinearGroup (Fin 4) F}
    (hH : ∀ y, y ∈ JK F hl ↔ proj 4 F H * y * (proj 4 F H)⁻¹ ∈ JK F hl) :
    (H : Matrix (Fin 4) (Fin 4) F) * kZero l = kZero l * H ∨
      (H : Matrix (Fin 4) (Fin 4) F) * kZero l = -(kZero l * H) := by
  set Hm := (H : Matrix (Fin 4) (Fin 4) F) with hHm
  set Hi := ((H⁻¹ : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hHi
  have hHH : Hm * Hi = 1 := by
    rw [hHm, hHi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hHH' : Hi * Hm = 1 := by
    rw [hHm, hHi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hcomm : ∀ u ∈ SK F hl, (Hi * u * Hm) * kZero l = kZero l * (Hi * u * Hm) := by
    intro u hu
    have h1 : proj 4 F (H⁻¹ * u * H) ∈ JK F hl := by
      rw [hH, map_mul, map_mul, map_inv]
      have e : proj 4 F H * ((proj 4 F H)⁻¹ * proj 4 F u * proj 4 F H) * (proj 4 F H)⁻¹ =
          proj 4 F u := by group
      rw [e]
      exact ⟨u, hu, rfl⟩
    obtain ⟨W, hW, hWe⟩ := h1
    have hWs : W⁻¹ * (H⁻¹ * u * H) ∈ scalars 4 F := proj_eq_proj_iff.1 hWe
    obtain ⟨c, -, hc⟩ := mem_scalars.1 hWs
    have hWC := (mem_CK_iff hl).1 (mem_CK_of_mem_SK hl hW)
    have e1 : ((H⁻¹ * u * H : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        (W : Matrix (Fin 4) (Fin 4) F) * Matrix.scalar (Fin 4) (c : F) := by
      rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have e2 : Hi * u * Hm = (W : Matrix (Fin 4) (Fin 4) F) * Matrix.scalar (Fin 4) (c : F) := by
      rw [← e1, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [e2, Matrix.mul_assoc,
      (Matrix.scalar_commute (c : F) (fun r' => Commute.all _ r') (kZero l)).eq,
      ← Matrix.mul_assoc, hWC, Matrix.mul_assoc]
  set Y := Hm * kZero l * Hi with hY
  have hYc : ∀ u ∈ SK F hl, Y * u = (u : Matrix (Fin 4) (Fin 4) F) * Y := by
    intro u hu
    have h1 := hcomm u hu
    have e1 : Y * u = Hm * (kZero l * (Hi * u * Hm)) * Hi := by
      rw [hY]
      simp only [Matrix.mul_assoc]
      rw [hHH, Matrix.mul_one]
    have e2 : Hm * ((Hi * u * Hm) * kZero l) * Hi = (u : Matrix (Fin 4) (Fin 4) F) * Y := by
      rw [hY]
      simp only [← Matrix.mul_assoc]
      rw [hHH, Matrix.one_mul]
    rw [e1, ← h1, e2]
  have hYeq := eq_of_comm_uK hl (hYc _ (slUK_mem_SK hl hl1 1 0))
    (hYc _ (slLK_mem_SK hl hl1 1 0)) (hYc _ (slUK_mem_SK hl hl1 0 1))
  set a := Y 0 0
  set b := Y 1 0
  have hYe : Y = eK l a b := by rw [hYeq, smul_one_add_smul_kZero]
  have hYsq : Y * Y = l • (1 : Matrix (Fin 4) (Fin 4) F) := by
    have e : Y * Y = Hm * (kZero l * kZero l) * Hi := by
      rw [hY]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Hi Hm, hHH', Matrix.one_mul]
    rw [e, kZero_mul_kZero, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hHH]
  rw [hYe, eK_mul_eK] at hYsq
  have e00 := congrFun (congrFun hYsq 0) 0
  have e10 := congrFun (congrFun hYsq 1) 0
  simp [eK] at e00 e10
  have ha : a = 0 := by
    have hab : a * b = 0 := by
      have : (2 : F) * (a * b) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_left h2
    rcases mul_eq_zero.1 hab with h | h
    · exact h
    · exfalso
      rw [h] at e00
      exact hns ⟨a, by linear_combination -e00⟩
  rw [ha] at e00
  have hb2 : b * b = 1 := by
    have : l * (b * b - 1) = 0 := by linear_combination e00
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hl)
  have hYK : Y = b • kZero l := by rw [hYe, ha, eK_zero_left]
  have hHK : Hm * kZero l = (b • kZero l) * Hm := by
    rw [← hYK, hY, Matrix.mul_assoc, hHH', Matrix.mul_one]
  rcases mul_self_eq_one_iff.mp hb2 with hb | hb
  · left
    rw [hHK, hb, one_smul]
  · right
    rw [hHK, hb, neg_one_smul, Matrix.neg_mul]

end OCL

end CFSG.ComponentClassification.CatFactsL4U4
