module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InvClassLa

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace InvClassL

open Matrix TBlocks HBlocks CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type} [Field F]

@[expose] def negOne2 : SpecialLinearGroup (Fin 2) F := ⟨-1, by simp [Matrix.det_neg]⟩

@[expose] def negOne4 : SpecialLinearGroup (Fin 4) F :=
  ⟨-1, by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩

theorem negOne2_sq : (negOne2 : SpecialLinearGroup (Fin 2) F) ^ 2 = 1 := by
  rw [pow_two]
  apply Subtype.ext
  change (-1 : Matrix (Fin 2) (Fin 2) F) * (-1) = 1
  rw [neg_mul_neg, Matrix.one_mul]

theorem proj_negOne4 : proj 4 F negOne4 = 1 := by
  rw [proj_eq_one_iff, mem_scalars]
  refine ⟨-1, by norm_num, ?_⟩
  change (-1 : Matrix (Fin 4) (Fin 4) F) = scalar (Fin 4) ((-1 : Fˣ) : F)
  rw [Units.val_neg, Units.val_one, scalar_apply, ← smul_one_eq_diagonal, neg_smul, one_smul]

theorem proj_ne_one_of_off {g : SpecialLinearGroup (Fin 4) F} {i j : Fin 4} (hij : i ≠ j)
    (h : (g : Matrix (Fin 4) (Fin 4) F) i j ≠ 0) : proj 4 F g ≠ 1 := by
  intro h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  rw [hc, scalar_apply, diagonal_apply_ne _ hij] at h
  exact h rfl

theorem proj_ne_one_of_diag {g : SpecialLinearGroup (Fin 4) F} {i j : Fin 4}
    (h : (g : Matrix (Fin 4) (Fin 4) F) i i ≠ (g : Matrix (Fin 4) (Fin 4) F) j j) :
    proj 4 F g ≠ 1 := by
  intro h1
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 h1)
  rw [hc, scalar_apply, diagonal_apply_eq, diagonal_apply_eq] at h
  exact h rfl

theorem eq_smul_of_proj_eq {A B : SpecialLinearGroup (Fin 4) F} (h : proj 4 F A = proj 4 F B) :
    ∃ c : F, (B : Matrix (Fin 4) (Fin 4) F) = c • (A : Matrix (Fin 4) (Fin 4) F) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  refine ⟨(c : F), ?_⟩
  have h1 : B = A * (A⁻¹ * B) := (mul_inv_cancel_left A B).symm
  calc (B : Matrix (Fin 4) (Fin 4) F) =
        ((A * (A⁻¹ * B) : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [← h1]
    _ = (A : Matrix (Fin 4) (Fin 4) F) *
        ((A⁻¹ * B : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) :=
          Matrix.SpecialLinearGroup.coe_mul _ _
    _ = (c : F) • (A : Matrix (Fin 4) (Fin 4) F) := by
          rw [hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

@[expose] def jSL : SpecialLinearGroup (Fin 2) F := ⟨jj, by simp [jj, Matrix.det_fin_two]⟩

theorem jSL_sq : jSL (F := F) ^ 2 = negOne2 := by
  rw [pow_two]
  apply Subtype.ext
  change (jj : Matrix (Fin 2) (Fin 2) F) * jj = -1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jj, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def bdSL : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →*
    SpecialLinearGroup (Fin 4) F where
  toFun x := ⟨bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F), by
    rw [det_bd, x.1.2, x.2.2, mul_one]⟩
  map_one' := Subtype.ext bd_one
  map_mul' x y := Subtype.ext (by
    change bd _ _ = bd _ _ * bd _ _
    rw [bd_mul]
    rfl)

theorem coe_bdSL (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((bdSL x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      bd (x.1 : Matrix (Fin 2) (Fin 2) F) (x.2 : Matrix (Fin 2) (Fin 2) F) := rfl

theorem bdSL_comm (x : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F) :
    ((bdSL x : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * X1 1 =
      X1 1 * (bdSL x : Matrix (Fin 4) (Fin 4) F) :=
  bd_comm_X1 _ _ 1

theorem bdSL_negOne : bdSL ((negOne2, negOne2) : SpecialLinearGroup (Fin 2) F × _) =
    negOne4 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [coe_bdSL]
    fin_cases i <;> fin_cases j <;> simp [bd, negOne2, negOne4]

theorem bd_z4z2 (h2 : (2 : F) ≠ 0) :
    orderOf (proj 4 F (bdSL (jSL, 1))) = 4 ∧ orderOf (proj 4 F (bdSL (jSL, jSL))) = 2 ∧
      Commute (proj 4 F (bdSL (jSL, 1))) (proj 4 F (bdSL (jSL, jSL))) ∧
      proj 4 F (bdSL (jSL, jSL)) ≠ proj 4 F (bdSL (jSL, 1)) ^ 2 := by
  have hx2 : proj 4 F (bdSL (jSL, 1)) ^ 2 = proj 4 F (bdSL (negOne2, 1)) := by
    rw [← map_pow, ← map_pow, Prod.pow_mk, jSL_sq, one_pow]
  have h00 : ((bdSL (negOne2, 1) : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) 0 0 = -1 := by
    rw [coe_bdSL]; simp [bd, negOne2]
  have h22 : ((bdSL (negOne2, 1) : SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) 2 2 = 1 := by
    rw [coe_bdSL]; simp [bd]
  have hne2 : proj 4 F (bdSL (negOne2, 1)) ≠ 1 := by
    refine proj_ne_one_of_diag (i := 0) (j := 2) ?_
    rw [h00, h22]
    intro h
    apply h2
    linear_combination -h
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, hx2]
      exact hne2
    · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hx2, ← map_pow, ← map_pow, Prod.pow_mk,
        negOne2_sq, one_pow, Prod.mk_one_one, map_one, map_one]
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← map_pow, Prod.pow_mk, jSL_sq, bdSL_negOne, proj_negOne4]
    · refine proj_ne_one_of_off (i := 0) (j := 1) (by decide) ?_
      rw [coe_bdSL]
      simp [bd, jSL, jj]
  · rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← map_mul, ← map_mul, Prod.mk_mul_mk,
      Prod.mk_mul_mk, one_mul, mul_one]
  · rw [hx2]
    intro h
    obtain ⟨c, hc⟩ := eq_smul_of_proj_eq h
    have h00 := congrFun (congrFun hc 0) 0
    rw [coe_bdSL, coe_bdSL] at h00
    simp [bd, jSL, jj, negOne2] at h00

theorem block_comm (g : SpecialLinearGroup (Fin 3) F) :
    ((blockSL F 3 1 g : SpecialLinearGroup (Fin (3 + 1)) F) : Matrix (Fin 4) (Fin 4) F) *
      dOne = dOne * (blockSL F 3 1 g : Matrix (Fin 4) (Fin 4) F) := by
  rw [coe_blockSL, dOne]
  exact blockGL_mul_diagonal_comm _ fun i j => by
    simp only [finSumFinEquiv_apply_left, Fin.val_castAdd, Fin.is_lt, ↓reduceIte]

@[expose] def diag3 (a b c : F) (h : a * b * c = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal ![a, b, c], by rw [det_diagonal, Fin.prod_univ_three]; simpa using h⟩

theorem blockSL_diag3_apply (a b c : F) (h : a * b * c = 1) (i : Fin 4) :
    ((blockSL F 3 1 (diag3 a b c h) : SpecialLinearGroup (Fin (3 + 1)) F) :
      Matrix (Fin 4) (Fin 4) F) i i = ![a, b, c, 1] i := by
  rw [coe_blockSL, coe_blockGL]
  fin_cases i <;> rfl

theorem diag3_mul (a b c a' b' c' : F) (h : a * b * c = 1) (h' : a' * b' * c' = 1)
    (h'' : (a * a') * (b * b') * (c * c') = 1) :
    diag3 a b c h * diag3 a' b' c' h' = diag3 (a * a') (b * b') (c * c') h'' := by
  apply Subtype.ext
  change diagonal ![a, b, c] * diagonal ![a', b', c'] = diagonal ![a * a', b * b', c * c']
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diag3_eq_one (a b c : F) (h : a * b * c = 1) (ha : a = 1) (hb : b = 1) (hc : c = 1) :
    diag3 a b c h = 1 := by
  subst ha hb hc
  apply Subtype.ext
  change diagonal ![(1 : F), 1, 1] = 1
  rw [← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem diag3_comm (a b c a' b' c' : F) (h : a * b * c = 1) (h' : a' * b' * c' = 1) :
    Commute (diag3 a b c h) (diag3 a' b' c' h') := by
  rw [Commute, SemiconjBy, diag3_mul _ _ _ _ _ _ _ _ (by linear_combination (b' * c' * a') * h
    + h'), diag3_mul _ _ _ _ _ _ _ _ (by linear_combination (b * c * a) * h' + h)]
  congr 1 <;> ring

theorem block_involution (h2 : (2 : F) ≠ 0) :
    orderOf (proj 4 F (blockSL F 3 1 (diag3 (-1) (-1) 1 (by ring)))) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← map_pow, pow_two, diag3_mul _ _ _ _ _ _ _ _ (by ring),
      diag3_eq_one _ _ _ _ (by ring) (by ring) (by ring), map_one, map_one]
  · refine proj_ne_one_of_diag (i := 0) (j := 3) ?_
    rw [blockSL_diag3_apply, blockSL_diag3_apply]
    intro h
    apply h2
    simp at h
    linear_combination -h

theorem block_z4z2 (h2 : (2 : F) ≠ 0) {i : F} (hi : i * i = -1) :
    orderOf (proj 4 F (blockSL F 3 1 (diag3 i (-i) 1 (by linear_combination -hi)))) = 4 ∧
      orderOf (proj 4 F (blockSL F 3 1 (diag3 (-1) 1 (-1) (by ring)))) = 2 ∧
      Commute (proj 4 F (blockSL F 3 1 (diag3 i (-i) 1 (by linear_combination -hi))))
        (proj 4 F (blockSL F 3 1 (diag3 (-1) 1 (-1) (by ring)))) ∧
      proj 4 F (blockSL F 3 1 (diag3 (-1) 1 (-1) (by ring))) ≠
        proj 4 F (blockSL F 3 1 (diag3 i (-i) 1 (by linear_combination -hi))) ^ 2 := by
  have hii : i * i * (-i * -i) * (1 * 1) = 1 := by
    rw [show -i * -i = i * i by ring, hi]
    norm_num
  have hsq : proj 4 F (blockSL F 3 1 (diag3 i (-i) 1 (by linear_combination -hi))) ^ 2 =
      proj 4 F (blockSL F 3 1 (diag3 (-1) (-1) 1 (by ring))) := by
    rw [← map_pow, ← map_pow, pow_two, diag3_mul _ _ _ _ _ _ _ _ hii]
    congr 2
    apply Subtype.ext
    change diagonal ![i * i, -i * -i, 1 * 1] = diagonal ![-1, -1, 1]
    congr 1
    funext k
    fin_cases k
    · exact hi
    · change -i * -i = -1
      linear_combination hi
    · exact mul_one 1
  have hinv := block_involution (F := F) h2
  have hy1 : proj 4 F (blockSL F 3 1 (diag3 (-1) (-1) 1 (by ring))) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hinv
    exact absurd hinv (by norm_num)
  have hy2 : proj 4 F (blockSL F 3 1 (diag3 (-1) (-1) 1 (by ring))) ^ 2 = 1 := by
    rw [← hinv]
    exact pow_orderOf_eq_one _
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, hsq]
      exact hy1
    · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hsq]
      exact hy2
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← map_pow, pow_two, diag3_mul _ _ _ _ _ _ _ _ (by ring),
        diag3_eq_one _ _ _ _ (by ring) (by ring) (by ring), map_one, map_one]
    · refine proj_ne_one_of_diag (i := 0) (j := 3) ?_
      rw [blockSL_diag3_apply, blockSL_diag3_apply]
      intro h
      apply h2
      simp at h
      linear_combination -h
  · exact ((diag3_comm _ _ _ _ _ _ _ _).map (blockSL F 3 1)).map (proj 4 F)
  · rw [hsq]
    intro h
    obtain ⟨c, hc⟩ := eq_smul_of_proj_eq h
    have h11 := congrFun (congrFun hc 1) 1
    have h33 := congrFun (congrFun hc 3) 3
    rw [Matrix.smul_apply, blockSL_diag3_apply, blockSL_diag3_apply] at h11 h33
    simp at h11 h33
    apply h2
    linear_combination h33 - h11

@[expose] def kronM (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 4) (Fin 4) F :=
  !![g 0 0, 0, g 0 1, 0; 0, g 0 0, 0, g 0 1; g 1 0, 0, g 1 1, 0; 0, g 1 0, 0, g 1 1]

theorem kronM_mul (g h : Matrix (Fin 2) (Fin 2) F) : kronM g * kronM h = kronM (g * h) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronM, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two]

theorem kronM_one : kronM (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kronM]

theorem det_kronM (g : Matrix (Fin 2) (Fin 2) F) : (kronM g).det = g.det ^ 2 := by
  rw [kronM, Matrix.det_succ_row_zero, Matrix.det_fin_two]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem kronM_comm (g : Matrix (Fin 2) (Fin 2) F) (c : F) :
    kronM g * stdN c = stdN c * kronM g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kronM, stdN, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

@[expose] def kronSL : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 4) F where
  toFun g := ⟨kronM (g : Matrix (Fin 2) (Fin 2) F), by rw [det_kronM, g.2, one_pow]⟩
  map_one' := Subtype.ext kronM_one
  map_mul' g h := Subtype.ext (by
    change kronM _ = kronM _ * kronM _
    rw [kronM_mul]
    rfl)

theorem coe_kronSL (g : SpecialLinearGroup (Fin 2) F) :
    ((kronSL g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      kronM (g : Matrix (Fin 2) (Fin 2) F) := rfl

theorem kronSL_comm (g : SpecialLinearGroup (Fin 2) F) (c : F) :
    ((kronSL g : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * stdN c =
      stdN c * (kronSL g : Matrix (Fin 4) (Fin 4) F) :=
  kronM_comm _ c

theorem kronSL_negOne : kronSL (negOne2 : SpecialLinearGroup (Fin 2) F) = negOne4 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    rw [coe_kronSL]
    fin_cases i <;> fin_cases j <;> simp [kronM, negOne2, negOne4]

theorem kron_involution : orderOf (proj 4 F (kronSL jSL)) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← map_pow, jSL_sq, kronSL_negOne, proj_negOne4]
  · refine proj_ne_one_of_off (i := 0) (j := 2) (by decide) ?_
    rw [coe_kronSL]
    simp [kronM, jSL, jj]

end InvClassL

end CFSG.ComponentClassification.CatFactsL4U4
