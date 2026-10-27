module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessA
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieV2

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

theorem wb_key {F : Type} [Field F] (a0 a1 b00 b01 b10 b11 : F) (hB : b00 * b11 - b01 * b10 = 1)
    (h0 : a0 ^ 4 = a0) (h1 : a1 ^ 4 = a1) (two : (2 : F) = 0) :
    ((a0 * b00 + a1 * b10) * (a0 * b01 + a1 * b11)) ^ 2 =
      (a0 * a1) ^ 2 + a0 * (b00 * b01) ^ 2 + a1 * (b10 * b11) ^ 2 := by
  linear_combination (b00 * b01) ^ 2 * h0 + (b10 * b11) ^ 2 * h1
    + (a0 * a1) ^ 2 * (b00 * b11 + b01 * b10 + 1) * hB
    + (a0 ^ 2 * a1 ^ 2 * b00 * b01 * b10 * b11
      + (a0 ^ 2 * b00 * b01 + a1 ^ 2 * b10 * b11) * (a0 * a1) * (b00 * b11 + b01 * b10)
      + (a0 * a1) ^ 2 * (b00 * b11 + b01 * b10 + 1) * (b01 * b10)) * two

theorem wb_frob4 {F : Type} [Field F] (hq : Nat.card F = 4) (x : F) : x ^ 4 = x := by
  by_cases hx : x = 0
  · simp [hx]
  · have h3 := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.pow_three_eq_one hq hx
    calc x ^ 4 = x * x ^ 3 := by ring
      _ = x := by rw [h3, mul_one]

theorem wb_mul_00 {F : Type} [Field F] (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A * B).1 0 0 = A.1 0 0 * B.1 0 0 + A.1 0 1 * B.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem wb_mul_01 {F : Type} [Field F] (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A * B).1 0 1 = A.1 0 0 * B.1 0 1 + A.1 0 1 * B.1 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem wb_mul_10 {F : Type} [Field F] (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A * B).1 1 0 = A.1 1 0 * B.1 0 0 + A.1 1 1 * B.1 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem wb_mul_11 {F : Type} [Field F] (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A * B).1 1 1 = A.1 1 0 * B.1 0 1 + A.1 1 1 * B.1 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def wbAct {F : Type} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : F × F) :
    F × F :=
  (A.1 0 0 * v.1 + A.1 0 1 * v.2, A.1 1 0 * v.1 + A.1 1 1 * v.2)

@[expose] def wbD {F : Type} [Field F] (κ : F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    F × F :=
  (κ * (A.1 0 0 * A.1 0 1) ^ 2, κ * (A.1 1 0 * A.1 1 1) ^ 2)

theorem wbD_mul {F : Type} [Field F] [CharP F 2] (hq : Nat.card F = 4) (κ : F)
    (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    wbD κ (A * B) = wbD κ A + wbAct A (wbD κ B) := by
  have hB : B.1 0 0 * B.1 1 1 - B.1 0 1 * B.1 1 0 = 1 := by
    have h := B.2
    rw [Matrix.det_fin_two] at h
    exact h
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have k0 := wb_key (A.1 0 0) (A.1 0 1) (B.1 0 0) (B.1 0 1) (B.1 1 0) (B.1 1 1) hB
    (wb_frob4 hq _) (wb_frob4 hq _) two
  have k1 := wb_key (A.1 1 0) (A.1 1 1) (B.1 0 0) (B.1 0 1) (B.1 1 0) (B.1 1 1) hB
    (wb_frob4 hq _) (wb_frob4 hq _) two
  unfold wbD wbAct
  rw [wb_mul_00, wb_mul_01, wb_mul_10, wb_mul_11]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add]
    linear_combination κ * k0
  · simp only [Prod.snd_add]
    linear_combination κ * k1

section Blocks

variable {F : Type} [Field F] [CharP F 2]

@[expose] def wbEmbMat (A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A.1 0 0, A.1 0 1, 0; A.1 1 0, A.1 1 1, 0; 0, 0, 1]

theorem wbEmbMat_det (A : Matrix.SpecialLinearGroup (Fin 2) F) : (wbEmbMat A).det = 1 := by
  have h := A.2
  rw [Matrix.det_fin_two] at h
  rw [wbEmbMat, Matrix.det_fin_three]
  simp
  linear_combination h

@[expose] def wbEmb (A : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨wbEmbMat A, wbEmbMat_det A⟩

theorem wbEmbMat_mul (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    wbEmbMat (A * B) = wbEmbMat A * wbEmbMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wbEmbMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three, wb_mul_00,
      wb_mul_01, wb_mul_10, wb_mul_11]

theorem wbEmb_mul (A B : Matrix.SpecialLinearGroup (Fin 2) F) :
    wbEmb (A * B) = wbEmb A * wbEmb B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact wbEmbMat_mul A B

theorem wbEmb_one : wbEmb (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wbEmb, wbEmbMat]

@[expose] def wbK (A : Matrix.SpecialLinearGroup (Fin 2) F) : projectiveSL 3 F :=
  proj 3 F (wbEmb A)

theorem wbK_mul (A B : Matrix.SpecialLinearGroup (Fin 2) F) : wbK (A * B) = wbK A * wbK B := by
  unfold wbK
  rw [wbEmb_mul, map_mul]

theorem wbK_one : wbK (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  unfold wbK
  rw [wbEmb_one, map_one]

@[expose] def wbV (v : F × F) : projectiveSL 3 F := yP v.2 * wP v.1

theorem wbV_mem_V2 (v : F × F) : wbV v ∈ V2 :=
  mem_V2.mpr ⟨v.2, v.1, rfl⟩

theorem wbV_mem_Ln [Finite F] (v : F × F) : wbV v ∈ Ln F :=
  Subgroup.le_normalizer (wbV_mem_V2 v)

theorem wbV_add (v w : F × F) : wbV (v + w) = wbV v * wbV w := by
  unfold wbV
  rw [V2_mul]
  rfl

theorem wbV_zero : wbV (0 : F × F) = 1 := by
  unfold wbV
  simp [yP_zero, wP_zero]

theorem wbK_mem_Ln [Finite F] (A : Matrix.SpecialLinearGroup (Fin 2) F) : wbK A ∈ Ln F := by
  change wbK A ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))
  rw [CFSG.Quasithin.H13.F431.L3.P3.normalizer_V2_eq]
  refine Subgroup.mem_map.mpr ⟨wbEmb A, ?_, rfl⟩
  refine CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mpr ⟨?_, ?_⟩ <;>
    simp [wbEmb, wbEmbMat]

@[expose] def wbBlock (v : F × F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![A.1 0 0, A.1 0 1, v.1; A.1 1 0, A.1 1 1, v.2; 0, 0, 1], by
    have h := A.2
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_three]
    simp
    linear_combination h⟩

theorem yM_mul_wM_mul_embMat (b c : F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    yM b * wM c * wbEmbMat A =
      !![A.1 0 0, A.1 0 1, c; A.1 1 0, A.1 1 1, b; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, wM, wbEmbMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wbV_mul_wbK (v : F × F) (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    wbV v * wbK A = proj 3 F (wbBlock v A) := by
  unfold wbV wbK yP wP
  simp only [← map_mul]
  congr 1
  apply Subtype.ext
  change yM v.2 * wM v.1 * wbEmbMat A = (wbBlock v A).1
  rw [yM_mul_wM_mul_embMat]
  rfl

theorem wbK_mul_wbV (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : F × F) :
    wbK A * wbV v = wbV (wbAct A v) * wbK A := by
  unfold wbK wbV yP wP
  simp only [← map_mul]
  congr 1
  apply Subtype.ext
  change wbEmbMat A * (yM v.2 * wM v.1) = yM (wbAct A v).2 * wM (wbAct A v).1 * wbEmbMat A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wbAct, yM, wM, wbEmbMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem wbK_conj_wbV (A : Matrix.SpecialLinearGroup (Fin 2) F) (v : F × F) :
    wbK A * wbV v * (wbK A)⁻¹ = wbV (wbAct A v) := by
  rw [wbK_mul_wbV, mul_inv_cancel_right]

theorem sl3_eq_of_proj_eq {X Y : Matrix.SpecialLinearGroup (Fin 3) F} (hX : X.1 2 2 = 1)
    (hY : Y.1 2 2 = 1) (h : proj 3 F X = proj 3 F Y) : X = Y := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_proj_iff.mp h)
  have hm : (X * (X⁻¹ * Y)).1 = X.1 * (X⁻¹ * Y).1 := Matrix.SpecialLinearGroup.coe_mul _ _
  rw [mul_inv_cancel_left, hc] at hm
  have hij : ∀ i j, Y.1 i j = X.1 i j * (c : F) := by
    intro i j
    have := congrFun (congrFun hm i) j
    simpa [Matrix.scalar_apply, Matrix.mul_diagonal] using this
  have hc1 : (c : F) = 1 := by
    have h22 := hij 2 2
    rw [hX, hY, one_mul] at h22
    exact h22.symm
  apply Subtype.ext
  ext i j
  rw [hij i j, hc1, mul_one]

theorem wbV_mul_wbK_inj {v w : F × F} {A B : Matrix.SpecialLinearGroup (Fin 2) F}
    (h : wbV v * wbK A = wbV w * wbK B) : v = w ∧ A = B := by
  rw [wbV_mul_wbK, wbV_mul_wbK] at h
  have hX : (wbBlock v A).1 2 2 = 1 := by simp [wbBlock]
  have hY : (wbBlock w B).1 2 2 = 1 := by simp [wbBlock]
  have e := congrArg Subtype.val (sl3_eq_of_proj_eq hX hY h)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  simp [wbBlock] at e00 e01 e10 e11 e02 e12
  refine ⟨Prod.ext e02 e12, Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

theorem ln_normal_form [Finite F] (hq : Nat.card F = 4) {g : projectiveSL 3 F} (hg : g ∈ Ln F) :
    ∃ (v : F × F) (A : Matrix.SpecialLinearGroup (Fin 2) F), g = wbV v * wbK A := by
  change g ∈ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))
    at hg
  rw [CFSG.Quasithin.H13.F431.L3.P3.normalizer_V2_eq] at hg
  obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨h20, h21⟩ := CFSG.Quasithin.H13.F431.L3.P3.mem_Q3_one_iff.mp hM
  have hD : (M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * M.1 2 2 = 1 := by
    have h := M.2
    rw [Matrix.det_fin_three, h20, h21] at h
    linear_combination h
  have hd0 : M.1 2 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hD
    exact zero_ne_one hD
  have h3 : (M.1 2 2) ^ 3 = 1 := LinearFieldFour.pow_three_eq_one hq hd0
  set lam : F := (M.1 2 2)⁻¹ with hlam_def
  have hlamd : lam * M.1 2 2 = 1 := inv_mul_cancel₀ hd0
  have hlam3 : lam ^ 3 = 1 := by
    rw [hlam_def, inv_pow, h3, inv_one]
  have hlam0 : lam ≠ 0 := inv_ne_zero hd0
  set lamU : Fˣ := Units.mk0 lam hlam0 with hlamU_def
  have hlamU3 : lamU ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hlam3
  set A : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨!![lam * M.1 0 0, lam * M.1 0 1; lam * M.1 1 0, lam * M.1 1 1], by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
      linear_combination lam ^ 3 * hD - lam ^ 2 * (M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0) * hlamd
        + hlam3⟩ with hA_def
  refine ⟨(lam * M.1 0 2, lam * M.1 1 2), A, ?_⟩
  have hM' : wbBlock (lam * M.1 0 2, lam * M.1 1 2) A =
      scalarElement lamU hlamU3 * M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [wbBlock, hA_def, coe_scalarElement, Matrix.scalar_apply, Matrix.diagonal_mul,
        Matrix.SpecialLinearGroup.coe_mul, hlamU_def, hlamd, h20, h21]
  rw [wbV_mul_wbK, hM', map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars lamU hlamU3),
    one_mul]

end Blocks

end CFSG.GH74.QTGen4.DSGen4.L34

end
