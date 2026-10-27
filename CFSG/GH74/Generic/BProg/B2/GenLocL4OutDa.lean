module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutDaCore
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtBasis

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section DaFrame

variable {F : Type} [Field F]

theorem comm_of_frame' {P : GL (Fin 4) F} {g G B : Matrix (Fin 4) (Fin 4) F}
    (hP : g * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * G) (hgB : g * B = B * gᵀ) :
    G * (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) =
      (((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * B * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ) * Gᵀ := by
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hGPi : Pi * g = G * Pi := by
    calc Pi * g = Pi * g * (Pm * Pi) := by rw [hPP, Matrix.mul_one]
      _ = Pi * (g * Pm) * Pi := by simp only [Matrix.mul_assoc]
      _ = (Pi * Pm) * G * Pi := by rw [hP]; simp only [Matrix.mul_assoc]
      _ = G * Pi := by rw [hPiP, Matrix.one_mul]
  have hGPi' : gᵀ * Piᵀ = Piᵀ * Gᵀ := by
    have := congrArg Matrix.transpose hGPi
    rw [Matrix.transpose_mul, Matrix.transpose_mul] at this
    exact this
  calc G * (Pi * B * Piᵀ) = (G * Pi) * B * Piᵀ := by simp only [Matrix.mul_assoc]
    _ = (Pi * g) * B * Piᵀ := by rw [hGPi]
    _ = Pi * (g * B) * Piᵀ := by simp only [Matrix.mul_assoc]
    _ = Pi * (B * gᵀ) * Piᵀ := by rw [hgB]
    _ = Pi * B * (gᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
    _ = Pi * B * (Piᵀ * Gᵀ) := by rw [hGPi']
    _ = (Pi * B * Piᵀ) * Gᵀ := by simp only [Matrix.mul_assoc]

theorem i0_eq : (GenLocL4Ext.i0 (-1 : F)) = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GenLocL4Ext.i0, bd2]

theorem xs_eq : (GenLocL4Ext.xs : Matrix (Fin 4) (Fin 4) F) = Gt := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GenLocL4Ext.xs, Gt]

theorem blk_form (B : Matrix (Fin 2) (Fin 2) F) (hs : B 0 1 = B 1 0)
    (hc : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * B = B * (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ) :
    B = !![B 0 0, B 0 1; B 0 1, -(B 0 0)] := by
  have e11 := congrFun (congrFun hc 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hs]
  linear_combination -e11

theorem da_split [Finite F] (hF4 : Nat.card F % 4 = 3) (B X i : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hBns : ¬ IsSquare B.det) (hXX : X * X = 1) (hX1 : X ≠ 1) (hXm1 : X ≠ -1)
    (hii : i * i = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F)) (hXi : X * i = i * X) (hXB : X * B = B * Xᵀ)
    (hiB : i * B = B * iᵀ) :
    ∃ (P0 : GL (Fin 4) F) (x1 y1 x2 y2 : F),
      B = (P0 : Matrix (Fin 4) (Fin 4) F) * bd2 !![x1, y1; y1, -x1] !![x2, y2; y2, -x2] * (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      i * (P0 : Matrix (Fin 4) (Fin 4) F) = (P0 : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] ∧
      X * (P0 : Matrix (Fin 4) (Fin 4) F) = (P0 : Matrix (Fin 4) (Fin 4) F) * Gt ∧
      ¬ IsSquare ((x1 ^ 2 + y1 ^ 2) * (x2 ^ 2 + y2 ^ 2)) := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨P0, hiP, hXP⟩ := GenLocL4Ext.exists_split_basis (not_isSquare_neg_one hF4) h2 i X (s := 1) one_ne_zero hii
    (by rw [hXX, one_mul, one_smul]) hXi.symm (by rw [one_smul]; exact hX1) (by rw [one_smul]; exact hXm1)
  rw [inv_one, one_smul, xs_eq] at hXP
  rw [i0_eq] at hiP
  have hGt : (Gt : Matrix (Fin 4) (Fin 4) F)ᵀ = Gt := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Gt]
  have hPP : (P0 : Matrix (Fin 4) (Fin 4) F) * ((P0⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P0
  have hPiP : ((P0⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P0 : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P0
  have hc1 := comm_of_frame hXP hGt hXB
  have hc2 := comm_of_frame' hiP hiB
  set Pm : Matrix (Fin 4) (Fin 4) F := (P0 : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P0⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  set B'' : Matrix (Fin 4) (Fin 4) F := Pi * B * Piᵀ with hB''
  have hB''t : B''ᵀ = B'' := by
    rw [hB'', Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hBt, Matrix.mul_assoc]
  obtain ⟨b02, b03, b12, b13, b20, b30, b21, b31⟩ := blocks_vanish Gt B'' h2 rfl hc1
  obtain ⟨B1, B2, hbd⟩ : ∃ B1 B2 : Matrix (Fin 2) (Fin 2) F, B'' = bd2 B1 B2 :=
    ⟨_, _, eq_bd2 B'' b02 b03 b12 b13 b20 b30 b21 b31⟩
  have hsym : bd2 B1ᵀ B2ᵀ = bd2 B1 B2 := by rw [← bd2_transpose, ← hbd, hB''t]
  obtain ⟨hB1t, hB2t⟩ := bd2_inj hsym
  rw [hbd, bd2_transpose, bd2_mul, bd2_mul] at hc2
  obtain ⟨hC1, hC2⟩ := bd2_inj hc2
  have hs1 : B1 0 1 = B1 1 0 := by simpa using (congrFun (congrFun hB1t 0) 1).symm
  have hs2 : B2 0 1 = B2 1 0 := by simpa using (congrFun (congrFun hB2t 0) 1).symm
  have hf1 := blk_form B1 hs1 hC1
  have hf2 := blk_form B2 hs2 hC2
  have hBeq : B = Pm * bd2 B1 B2 * Pmᵀ := by
    have hPt' : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
    rw [← hbd, hB'']
    calc B = (Pm * Pi) * B * (Piᵀ * Pmᵀ) := by rw [hPP, hPt', Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨P0, B1 0 0, B1 0 1, B2 0 0, B2 0 1, ?_, hiP, hXP, ?_⟩
  · rw [← hf1, ← hf2]; exact hBeq
  · intro hsq
    obtain ⟨z, hz⟩ := hsq
    apply hBns
    refine ⟨Pm.det * z, ?_⟩
    rw [hBeq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, bd2_det, hf1, hf2, Matrix.det_fin_two_of,
      Matrix.det_fin_two_of]
    have : (B1 0 0 ^ 2 + B1 0 1 ^ 2) * (B2 0 0 ^ 2 + B2 0 1 ^ 2) = z * z := hz
    linear_combination Pm.det * Pm.det * this

@[expose] def swapM : Matrix (Fin 4) (Fin 4) F := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem swapM_transpose : (swapM : Matrix (Fin 4) (Fin 4) F)ᵀ = swapM := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapM]

theorem swapM_bd2 (A B : Matrix (Fin 2) (Fin 2) F) : swapM * bd2 A B * swapM = bd2 B A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapM, bd2, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapM_Gt : (swapM : Matrix (Fin 4) (Fin 4) F) * Gt = -(Gt * swapM) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [swapM, Gt, Matrix.mul_apply, Fin.sum_univ_four]

theorem swapM_det : (swapM : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  simp [swapM, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem da_split2 [Finite F] (hF4 : Nat.card F % 4 = 3) (B X i : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hBns : ¬ IsSquare B.det) (hXX : X * X = 1) (hX1 : X ≠ 1) (hXm1 : X ≠ -1)
    (hii : i * i = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F)) (hXi : X * i = i * X) (hXB : X * B = B * Xᵀ)
    (hiB : i * B = B * iᵀ) :
    ∃ (P : GL (Fin 4) F) (x1 y1 x2 y2 : F),
      B = (P : Matrix (Fin 4) (Fin 4) F) * bd2 !![x1, y1; y1, -x1] !![x2, y2; y2, -x2] * (P : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      i * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] ∧
      (X * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gt ∨
        X * (P : Matrix (Fin 4) (Fin 4) F) = -((P : Matrix (Fin 4) (Fin 4) F) * Gt)) ∧
      IsSquare (x1 ^ 2 + y1 ^ 2) ∧ x1 ^ 2 + y1 ^ 2 ≠ 0 ∧ ¬ IsSquare (x2 ^ 2 + y2 ^ 2) := by
  obtain ⟨P0, x1, y1, x2, y2, hB, hi, hX, hns⟩ := da_split hF4 B X i hBt hBns hXX hX1 hXm1 hii hXi hXB hiB
  have hn1 : x1 ^ 2 + y1 ^ 2 ≠ 0 := fun h => hns ⟨0, by rw [h]; ring⟩
  have hn2 : x2 ^ 2 + y2 ^ 2 ≠ 0 := fun h => hns ⟨0, by rw [h]; ring⟩
  by_cases h1 : IsSquare (x1 ^ 2 + y1 ^ 2)
  · refine ⟨P0, x1, y1, x2, y2, hB, hi, Or.inl hX, h1, hn1, fun h2 => hns ?_⟩
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    exact ⟨a * b, by rw [ha, hb]; ring⟩
  · have h2 : IsSquare (x2 ^ 2 + y2 ^ 2) := by
      by_contra h2
      exact hns (isSquare_mul_of_not_isSquare h1 h2)
    have hdet : (swapM : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by rw [swapM_det]; exact one_ne_zero
    refine ⟨P0 * Matrix.GeneralLinearGroup.mkOfDetNeZero swapM hdet, x2, y2, x1, y1, ?_, ?_, ?_, h2, hn2, h1⟩
    · show B = ((P0 : Matrix (Fin 4) (Fin 4) F) * swapM) * bd2 !![x2, y2; y2, -x2] !![x1, y1; y1, -x1] *
        ((P0 : Matrix (Fin 4) (Fin 4) F) * swapM)ᵀ
      rw [Matrix.transpose_mul, swapM_transpose]
      calc B = (P0 : Matrix (Fin 4) (Fin 4) F) * bd2 !![x1, y1; y1, -x1] !![x2, y2; y2, -x2] * (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := hB
        _ = (P0 : Matrix (Fin 4) (Fin 4) F) * (swapM * bd2 !![x2, y2; y2, -x2] !![x1, y1; y1, -x1] * swapM) *
            (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := by rw [swapM_bd2]
        _ = _ := by simp only [Matrix.mul_assoc]
    · show i * ((P0 : Matrix (Fin 4) (Fin 4) F) * swapM) = ((P0 : Matrix (Fin 4) (Fin 4) F) * swapM) *
        bd2 !![0, -1; 1, 0] !![0, -1; 1, 0]
      have hsw : swapM * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * (swapM : Matrix (Fin 4) (Fin 4) F) := by
        ext a b; fin_cases a <;> fin_cases b <;> simp [swapM, bd2, Matrix.mul_apply, Fin.sum_univ_four]
      rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, ← hsw, ← Matrix.mul_assoc]
    · right
      show X * ((P0 : Matrix (Fin 4) (Fin 4) F) * swapM) = -(((P0 : Matrix (Fin 4) (Fin 4) F) * swapM) * Gt)
      have e : Gt * (swapM : Matrix (Fin 4) (Fin 4) F) = -(swapM * Gt) := by rw [swapM_Gt, neg_neg]
      rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc]

theorem rot_block [Finite F] (hF4 : Nat.card F % 4 = 3) (x y : F) (hs : IsSquare (x ^ 2 + y ^ 2))
    (hn0 : x ^ 2 + y ^ 2 ≠ 0) :
    ∃ κ v : F, κ ≠ 0 ∧ (!![x, y; y, -x] : Matrix (Fin 2) (Fin 2) F) =
      !![1, v; -v, 1] * (κ • !![0, 1; 1, 0]) * (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  have hK := ringChar_ne_two_of_card_mod hF4
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨s, hs⟩ := hs
  obtain ⟨t, ht2, hty⟩ : ∃ t : F, t * t = x ^ 2 + y ^ 2 ∧ y + t ≠ 0 := by
    by_cases h : y + s = 0
    · refine ⟨-s, by rw [hs]; ring, fun h' => ?_⟩
      have h3 : (2 : F) * s = 0 := by linear_combination h - h'
      have : s = 0 := (mul_eq_zero.1 h3).resolve_left h2
      apply hn0
      rw [hs, this]; ring
    · exact ⟨s, hs.symm, h⟩
  have hκ : (y + t) / 2 ≠ 0 := div_ne_zero hty h2
  refine ⟨(y + t) / 2, x / (y + t), hκ, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals first | ring1 | linear_combination ht2 | linear_combination (-1 : F) * ht2

theorem da_frame [Finite F] (hF4 : Nat.card F % 4 = 3) (B X i : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hBns : ¬ IsSquare B.det) (hXX : X * X = 1) (hX1 : X ≠ 1) (hXm1 : X ≠ -1)
    (hii : i * i = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F)) (hXi : X * i = i * X) (hXB : X * B = B * Xᵀ)
    (hiB : i * B = B * iᵀ) :
    ∃ (P : GL (Fin 4) F) (κ p q : F), κ ≠ 0 ∧ ¬ IsSquare (p ^ 2 + q ^ 2) ∧
      B = (P : Matrix (Fin 4) (Fin 4) F) * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (P : Matrix (Fin 4) (Fin 4) F)ᵀ ∧
      i * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] ∧
      (X * (P : Matrix (Fin 4) (Fin 4) F) = (P : Matrix (Fin 4) (Fin 4) F) * Gt ∨
        X * (P : Matrix (Fin 4) (Fin 4) F) = -((P : Matrix (Fin 4) (Fin 4) F) * Gt)) := by
  obtain ⟨P0, x1, y1, x2, y2, hB, hi, hX, hsq, hn0, hns2⟩ := da_split2 hF4 B X i hBt hBns hXX hX1 hXm1 hii hXi hXB hiB
  obtain ⟨κ, v, hκ, hQ⟩ := rot_block hF4 x1 y1 hsq hn0
  have hv : (1 : F) * 1 - v * (-v) ≠ 0 := fun h => by
    have := aniso2 hF4 (x := 1) (y := v) (by linear_combination h)
    exact one_ne_zero this.1
  have hdetQ : (bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1).det ≠ 0 := by
    rw [bd2_det, Matrix.det_fin_two_of, Matrix.det_one, mul_one]
    exact hv
  have hQC : (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = !![0, -1; 1, 0] * !![1, v; -v, 1] := by
    ext a b; fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hQm : bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1 =
      bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1 * bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
    rw [bd2_mul, bd2_mul, ← hQC]
    simp
  refine ⟨P0 * Matrix.GeneralLinearGroup.mkOfDetNeZero (bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) hdetQ,
    κ, x2, y2, hκ, hns2, ?_, ?_, ?_⟩
  · show B = ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) *
      bd2 (κ • !![0, 1; 1, 0]) !![x2, y2; y2, -x2] *
      ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1)ᵀ
    rw [Matrix.transpose_mul, bd2_transpose]
    calc B = (P0 : Matrix (Fin 4) (Fin 4) F) * bd2 !![x1, y1; y1, -x1] !![x2, y2; y2, -x2] * (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := hB
      _ = (P0 : Matrix (Fin 4) (Fin 4) F) * (bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1 *
          bd2 (κ • !![0, 1; 1, 0]) !![x2, y2; y2, -x2] *
          bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ (1 : Matrix (Fin 2) (Fin 2) F)ᵀ) *
          (P0 : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        rw [bd2_mul, bd2_mul, ← hQ]
        simp
      _ = _ := by simp only [Matrix.mul_assoc]
  · show i * ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) =
      ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) *
        bd2 !![0, -1; 1, 0] !![0, -1; 1, 0]
    rw [← Matrix.mul_assoc, hi, Matrix.mul_assoc, hQm, ← Matrix.mul_assoc]
  · have hGc : Gt * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1 = bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1 * Gt :=
      Gt_comm_bd2 _ _
    rcases hX with hX | hX
    · left
      show X * ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) =
        ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) * Gt
      rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hGc, ← Matrix.mul_assoc]
    · right
      show X * ((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) =
        -(((P0 : Matrix (Fin 4) (Fin 4) F) * bd2 (!![1, v; -v, 1] : Matrix (Fin 2) (Fin 2) F) 1) * Gt)
      rw [← Matrix.mul_assoc, hX, Matrix.neg_mul, Matrix.mul_assoc, hGc, ← Matrix.mul_assoc]

end DaFrame

section ClassDaThm

open CFSG.ComponentClassification.CatalogueBHigherLinearAction in
theorem classDa (F : Type) [Field F] [Finite F] : ClassDa F := by
  intro hF4 h7 B X i hBt hBdet hBd hXX hXdet hX1 hXm1 hii hXi hXB hiB Γ hP1 hP2 hP3
  obtain ⟨P, κ, p, q, hκ, hn, hBP, hiP, hXP⟩ := da_frame hF4 B X i hBt hBd hXX hX1 hXm1 hii hXi hXB hiB
  have hPP : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv P
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul P
  set Pm : Matrix (Fin 4) (Fin 4) F := (P : Matrix (Fin 4) (Fin 4) F)
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
  have hPt : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPt' : Pmᵀ * Piᵀ = 1 := by rw [← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
  have ei : Pi * i * Pm = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] := by
    rw [Matrix.mul_assoc, hiP, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have eB : Pi * B * Piᵀ = bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] := by
    rw [hBP]
    calc Pi * (Pm * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * Pmᵀ) * Piᵀ =
        (Pi * Pm) * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] * (Pmᵀ * Piᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hPiP, hPt', Matrix.one_mul, Matrix.mul_one]
  have eiB : Pi * (i * B) * Piᵀ = bd2 !![0, -1; 1, 0] !![0, -1; 1, 0] * bd2 (κ • !![0, 1; 1, 0]) !![p, q; q, -p] := by
    rw [← ei, ← eB]
    calc Pi * (i * B) * Piᵀ = Pi * i * (Pm * Pi) * B * Piᵀ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  have eX : Pi * X * Pm = Gt ∨ Pi * X * Pm = -Gt := by
    rcases hXP with h | h
    · left
      rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    · right
      rw [Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc, hPiP, Matrix.one_mul]
  have hcommX : ∀ z : SL(4, F), (z : Matrix (Fin 4) (Fin 4) F) * Gt = Gt * (z : Matrix (Fin 4) (Fin 4) F) →
      ((slConjugation 4 F P).toMonoidHom z : Matrix (Fin 4) (Fin 4) F) * X = X * ((slConjugation 4 F P).toMonoidHom z : Matrix (Fin 4) (Fin 4) F) := by
    intro z hz
    refine (conj_commute_iff P z X).2 ?_
    rcases eX with e | e
    · rw [e]; exact hz
    · rw [e, Matrix.mul_neg, Matrix.neg_mul, hz]
  refine top_of_conj Γ P (gen_Da_core hF4 h7 κ p q hκ hn (Γ.comap (slConjugation 4 F P).toMonoidHom) ?_ ?_ ?_)
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP1 _ (hcommX x hx1) ((conj_form_iff P x B).2 (by rw [eB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP2 _ (hcommX x hx1) ((conj_form_iff P x (i * B)).2 (by rw [eiB]; exact hx2))
  · intro x hx1 hx2
    show (slConjugation 4 F P).toMonoidHom x ∈ Γ
    exact hP3 _ ((conj_commute_iff P x i).2 (by rw [ei]; exact hx1)) ((conj_form_iff P x B).2 (by rw [eB]; exact hx2))

end ClassDaThm

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
