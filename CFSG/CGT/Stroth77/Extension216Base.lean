module

public import CFSG.CGT.Stroth77.TorusNormalForm
public import CFSG.CGT.Stroth77.Extension24Square

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem t330_k_pos {m : ℕ} (hm : 3 ≤ m) (i : Fin 3) :
    1 ≤ (StrothTypeIndex.t330 m hm).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type32x.k] <;> omega

theorem odd_iV_t330 (m : ℕ) : Odd (Type120.iV m) := by
  have h := Type120.three_mul_iV m
  have hodd : Odd ((2 : ℤ) ^ (2 * m + 1) + 1) :=
    Even.add_one (even_two.pow_of_ne_zero (by omega))
  rw [← h] at hodd
  exact (Int.odd_mul.mp hodd).2

theorem rho_apply_gens_t330 {m : ℕ} (hm : 3 ≤ m) (i j l : ℤ) :
    (StrothTypeIndex.t330 m hm).action.φρ
        (i • gen (StrothTypeIndex.t330 m hm).k 0 + j • gen (StrothTypeIndex.t330 m hm).k 1 +
          l • gen (StrothTypeIndex.t330 m hm).k 2) =
      (i - 4 * l) • gen (StrothTypeIndex.t330 m hm).k 0 +
        (-l) • gen (StrothTypeIndex.t330 m hm).k 1 +
          (j - l) • gen (StrothTypeIndex.t330 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp [StrothTypeIndex.action, Type330.actionPaper, Type330.action, SigmaFourAction.ofMatEq,
    Type330.ρM, ofCols_apply, sub_eq_add_neg, mul_comm]

theorem t_apply_gens_t330 {m : ℕ} (hm : 3 ≤ m) (i j l : ℤ) :
    (StrothTypeIndex.t330 m hm).action.φt
        (i • gen (StrothTypeIndex.t330 m hm).k 0 + j • gen (StrothTypeIndex.t330 m hm).k 1 +
          l • gen (StrothTypeIndex.t330 m hm).k 2) =
      ((4 - Type120.iV m) * i + 8 * Type120.GV m * Type120.iV m * j +
          (4 * Type120.FV m * Type120.iV m - 8 * Type120.iV m) * l) •
          gen (StrothTypeIndex.t330 m hm).k 0 +
        (i - 7 * Type120.iV m * j - 2 * Type120.iV m * l) •
          gen (StrothTypeIndex.t330 m hm).k 1 +
        ((2 + 2 ^ (m - 1)) * i - 8 * Type120.iV m * j - 7 * Type120.iV m * l) •
          gen (StrothTypeIndex.t330 m hm).k 2 := by
  rw [matAct_zsmul_gens]
  simp only [StrothTypeIndex.action, Type330.actionPaper, Type330.action,
    SigmaFourAction.ofMatEq, Type330.tM, Type330.uvA, Type330.ρM, ofCols_apply]
  congr 2
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ofCols_apply, -mul_eq_mul_right_iff,
      -mul_eq_mul_left_iff]
    ring
  · simp [ofCols_mulVec, ofCols_apply, -mul_eq_mul_right_iff, -mul_eq_mul_left_iff]
    ring

@[expose] def tBar330 (v : Fin 3 → ZMod 2) : Fin 3 → ZMod 2 := ![v 0, v 0 + v 1, v 2]

theorem parityTorus_rho_t330 {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t330 m hm).k) :
    parityTorus _ (t330_k_pos hm) ((StrothTypeIndex.t330 m hm).action.φρ y) =
      rhoBar300 (parityTorus _ (t330_k_pos hm) y) := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [rho_apply_gens_t330, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, h4, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parityTorus_t_t330 {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t330 m hm).k) :
    parityTorus _ (t330_k_pos hm) ((StrothTypeIndex.t330 m hm).action.φt y) =
      tBar330 (parityTorus _ (t330_k_pos hm) y) := by
  have hI2 : ((Type120.iV m : ℤ) : ZMod 2) = 1 :=
    ZMod.intCast_eq_one_iff_odd.mpr (odd_iV_t330 m)
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ y
  rw [t_apply_gens_t330, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h7 : (7 : ZMod 2) = 1 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  have hN : (2 : ZMod 2) ^ (m - 1) = 0 := by rw [h2]; exact zero_pow (by omega)
  funext r
  fin_cases r
  · simp [tBar330, hI2, h4, h8, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · simp [tBar330, hI2, h2, h7, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  · have hm1 : m - 1 ≠ 0 := by omega
    simp [tBar330, hI2, h2, h7, h8, hN, hm1, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem fixed_check_t330 : ∀ v : Fin 3 → ZMod 2, rhoBar300 v = v → tBar330 v = v → v = 0 := by
  unfold rhoBar300 tBar330
  decide

theorem rho_a_t330 {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t330 m hm).action.φρ (gen (StrothTypeIndex.t330 m hm).k 1) =
      gen (StrothTypeIndex.t330 m hm).k 2 := by
  have h1 := rho_apply_gens_t330 hm 0 1 0
  simpa using h1

theorem fix_torus_t330 {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t330 m hm).k)
    (hρ : (StrothTypeIndex.t330 m hm).action.φρ v = v)
    (ht : (StrothTypeIndex.t330 m hm).action.φt v = v) : v = 0 := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ v
  rw [rho_apply_gens_t330] at hρ
  rw [t_apply_gens_t330] at ht
  obtain ⟨-, hρ1, hρ2⟩ := zsmul_gens_dvd_of_eq hρ
  obtain ⟨-, ht1, -⟩ := zsmul_gens_dvd_of_eq ht
  change (2 : ℤ) ^ m ∣ _ at hρ1 hρ2 ht1
  have h3 : IsCoprime ((2 : ℤ) ^ m) 3 :=
    (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩).pow_left
  have hl : (2 : ℤ) ^ m ∣ l := by
    refine h3.dvd_of_dvd_mul_left ?_
    have := dvd_add hρ1 hρ2
    convert this using 1
    ring
  have hj : (2 : ℤ) ^ m ∣ j := by
    have := dvd_sub hρ1 hl
    convert this using 1
    ring
  have hi : (2 : ℤ) ^ m ∣ i := by
    have := dvd_sub (dvd_add (dvd_mul_of_dvd_right hj (1 + 7 * Type120.iV m))
      (dvd_mul_of_dvd_right hl (2 * Type120.iV m))) ht1
    convert this using 1
    ring
  have h0 := zsmul_gens_eq_of_dvd (k := (StrothTypeIndex.t330 m hm).k) (p := i) (q := j)
    (r := l) (p' := 0) (q' := 0) (r' := 0)
    (by change (2 : ℤ) ^ m ∣ 0 - i; rw [zero_sub, dvd_neg]; exact hi)
    (by change (2 : ℤ) ^ m ∣ 0 - j; rw [zero_sub, dvd_neg]; exact hj)
    (by change (2 : ℤ) ^ m ∣ 0 - l; rw [zero_sub, dvd_neg]; exact hl)
  rw [h0]
  simp

theorem fix4_torus_t330 {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t330 m hm).k)
    (hρ : ∃ z, 4 • z = (StrothTypeIndex.t330 m hm).action.φρ v - v)
    (ht : ∃ z, 4 • z = (StrothTypeIndex.t330 m hm).action.φt v - v) : ∃ z, 2 • z = v := by
  obtain ⟨i, j, l, rfl⟩ := torus_eq_zsmul_gens _ v
  obtain ⟨zρ, hzρ⟩ := hρ
  obtain ⟨zt, hzt⟩ := ht
  rw [rho_apply_gens_t330] at hzρ
  rw [t_apply_gens_t330] at hzt
  have h4 : ∀ r : Fin 3, (4 : ℤ) ∣ 2 ^ (StrothTypeIndex.t330 m hm).k r := by
    intro r
    have hr : (StrothTypeIndex.t330 m hm).k r = m := by fin_cases r <;> rfl
    rw [hr]
    exact ⟨2 ^ (m - 2), by rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega⟩
  have eρ : (i - 4 * l) • gen (StrothTypeIndex.t330 m hm).k 0 +
      (-l) • gen (StrothTypeIndex.t330 m hm).k 1 + (j - l) • gen (StrothTypeIndex.t330 m hm).k 2 -
      (i • gen (StrothTypeIndex.t330 m hm).k 0 + j • gen (StrothTypeIndex.t330 m hm).k 1 +
        l • gen (StrothTypeIndex.t330 m hm).k 2) =
      (-4 * l) • gen (StrothTypeIndex.t330 m hm).k 0 +
        (-l - j) • gen (StrothTypeIndex.t330 m hm).k 1 +
          (j - 2 * l) • gen (StrothTypeIndex.t330 m hm).k 2 := by
    module
  rw [eρ] at hzρ
  have hρ1 := dvd_four_of_eq_four_smul_coord 1 hzρ.symm (h4 1)
  have hρ2 := dvd_four_of_eq_four_smul_coord 2 hzρ.symm (h4 2)
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true,
    Fin.reduceEq] at hρ1 hρ2
  have hl : (4 : ℤ) ∣ l := by omega
  have hj : (4 : ℤ) ∣ j := by omega
  have et : ((4 - Type120.iV m) * i + 8 * Type120.GV m * Type120.iV m * j +
          (4 * Type120.FV m * Type120.iV m - 8 * Type120.iV m) * l) •
          gen (StrothTypeIndex.t330 m hm).k 0 +
        (i - 7 * Type120.iV m * j - 2 * Type120.iV m * l) •
          gen (StrothTypeIndex.t330 m hm).k 1 +
        ((2 + 2 ^ (m - 1)) * i - 8 * Type120.iV m * j - 7 * Type120.iV m * l) •
          gen (StrothTypeIndex.t330 m hm).k 2 -
      (i • gen (StrothTypeIndex.t330 m hm).k 0 + j • gen (StrothTypeIndex.t330 m hm).k 1 +
        l • gen (StrothTypeIndex.t330 m hm).k 2) =
      ((4 - Type120.iV m) * i + 8 * Type120.GV m * Type120.iV m * j +
          (4 * Type120.FV m * Type120.iV m - 8 * Type120.iV m) * l - i) •
          gen (StrothTypeIndex.t330 m hm).k 0 +
        (i - 7 * Type120.iV m * j - 2 * Type120.iV m * l - j) •
          gen (StrothTypeIndex.t330 m hm).k 1 +
        ((2 + 2 ^ (m - 1)) * i - 8 * Type120.iV m * j - 7 * Type120.iV m * l - l) •
          gen (StrothTypeIndex.t330 m hm).k 2 := by
    module
  rw [et] at hzt
  have ht1 := dvd_four_of_eq_four_smul_coord 1 hzt.symm (h4 1)
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, ite_true,
    Fin.reduceEq] at ht1
  obtain ⟨j', rfl⟩ := hj
  obtain ⟨l', rfl⟩ := hl
  obtain ⟨i', rfl⟩ : (4 : ℤ) ∣ i := by
    have := dvd_add ht1 (dvd_mul_right 4 (7 * Type120.iV m * j' + 2 * Type120.iV m * l' + j'))
    convert this using 1
    ring
  refine ⟨(2 * i') • gen (StrothTypeIndex.t330 m hm).k 0 +
    (2 * j') • gen (StrothTypeIndex.t330 m hm).k 1 +
      (2 * l') • gen (StrothTypeIndex.t330 m hm).k 2, ?_⟩
  rw [two_nsmul]
  module

theorem dbl_data_t130 {m : ℕ} {i F G N i' F' G' N' K' J' : ℤ} (h : Type32x.Data m i F G N)
    (h' : Type130.Data m i' F' G' N' K' J') :
    i = 8 * G + 19 ∧ F = 4 * G + 9 ∧ i' = 8 * (4 * G + 7) + 19 ∧ F' = 4 * (4 * G + 7) + 9 ∧
      G' = 4 * G + 7 ∧ N = 2 * J' ∧ N' = 4 * J' ∧ K' = 2 * J' ∧ 3 * G + 7 = 4 * J' * J' ∧
      (2 : ℤ) ^ m = 4 * J' ∧ (2 : ℤ) ^ (m + 1) = 8 * J' := by
  obtain ⟨hm, hi, hF, hG, hN⟩ := h
  obtain ⟨hi', hF', hN', hK', hJ', hG'⟩ := h'
  have h2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hNJ : N = 2 * J' := by
    have h2 : 2 * N = 2 * (2 * J') := by rw [hN, ← h2m, ← hN', hK', hJ']
    omega
  have hGJ : 3 * G + 7 = 4 * J' * J' := by rw [hG, hNJ]; ring
  have hGG : G' = 4 * G + 7 := by
    have h3 : 3 * (G' - (4 * G + 7)) = 0 := by
      rw [hK', hJ'] at hG'
      linear_combination hG' - 4 * hGJ
    omega
  have h0 : (2 : ℤ) ^ m = 4 * J' := by rw [← hN', hK', hJ']; ring
  refine ⟨hi, hF, by rw [hi', hGG], by rw [hF', hGG], hGG, hNJ, by rw [hK', hJ']; ring, hJ',
    hGJ, h0, by rw [pow_succ, h0]; ring⟩

theorem t330_dbl_t130_uvM {m : ℕ} {i F G N i' F' G' N' K' J' : ℤ}
    (h : Type32x.Data m i F G N) (h' : Type130.Data m i' F' G' N' K' J') :
    MatEq (Type130.k m) (Type130.uvM i' F' G' N' * Matrix.diagonal ![1, 2, 2])
      (Matrix.diagonal ![1, 2, 2] * Type330.uvM i F G N) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hG, h0, h1⟩ := dbl_data_t130 h h'
  refine MatEq.of_three_pow_witness (k := Type130.k m) 3
    (W := !![
      -216*J',
      23040*J'^3 - 144*J',
      -1548288*J'^5 - 184320*J'^4 - 437760*J'^3 + 1152*J'^2 - 3528*J';
      0,
      -1080*J',
      -46080*J'^4 - 345600*J'^3 + 288*J'^2 - 3456*J';
      0,
      432*J',
      -46080*J'^4 + 34560*J'^3 + 288*J'^2 + 864*J']) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type130.k, h0, h1, Type130.uvM, Type130.tM, Type130.uvA, Type130.ρM, Type130.uM, uMat,
      Type330.uvM, Type330.tM, Type330.uvA, Type330.ρM, Type330.uM, ofCols_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, -mul_eq_zero,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-216) * hG
    | linear_combination (23040*J'^2 + 17280*G + 40176) * hG
    | linear_combination (-1548288*J'^4 - 1161216*G*J'^2 - 184320*J'^3 - 870912*G^2
          - 138240*G*J' - 3147264*J'^2 - 4392576*G - 321408*J' - 5511240) * hG
    | linear_combination (-2160) * hG
    | linear_combination (-92160*J'^3 - 69120*G*J' - 691200*J'^2 - 518400*G - 160704*J'
          - 1216512) * hG
    | linear_combination (864) * hG
    | linear_combination (-92160*J'^3 - 69120*G*J' + 69120*J'^2 + 51840*G - 160704*J' + 122688) * hG
    | ring1

theorem t330_dbl_t130_tM {m : ℕ} {i F G N i' F' G' N' K' J' : ℤ}
    (h : Type32x.Data m i F G N) (h' : Type130.Data m i' F' G' N' K' J') :
    MatEq (Type130.k m) (Type130.tM i' F' G' N' * Matrix.diagonal ![1, 2, 2])
      (Matrix.diagonal ![1, 2, 2] * Type330.tM i F G N) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hG, h0, h1⟩ := dbl_data_t130 h h'
  refine MatEq.of_three_pow_witness (k := Type130.k m) 2
    (W := !![
      -72*J',
      3840*J'^3 - 1320*J',
      7680*J'^3 - 624*J';
      0,
      -504*J',
      -144*J';
      0,
      -576*J',
      -504*J']) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type130.k, h0, h1, Type130.uvM, Type130.tM, Type130.uvA, Type130.ρM, Type130.uM, uMat,
      Type330.uvM, Type330.tM, Type330.uvA, Type330.ρM, Type330.uM, ofCols_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, -mul_eq_zero,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-72) * hG
    | linear_combination (3840*J'^2 + 2880*G + 5400) * hG
    | linear_combination (7680*J'^2 + 5760*G + 12816) * hG
    | linear_combination (-1008) * hG
    | linear_combination (-288) * hG
    | linear_combination (-1152) * hG
    | ring1

theorem t330_dbl_t130_uM {m : ℕ} {i F G N i' F' G' N' K' J' : ℤ}
    (h : Type32x.Data m i F G N) (h' : Type130.Data m i' F' G' N' K' J') :
    MatEq (Type130.k m) (Type130.uM F' K' * Matrix.diagonal ![1, 2, 2])
      (Matrix.diagonal ![1, 2, 2] * Type330.uM F N) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hG, h0, h1⟩ := dbl_data_t130 h h'
  refine MatEq.of_three_pow_witness (k := Type130.k m) 1
    (W := !![0, -96*J', 192*J'^2 - 96*J'; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type130.k, h0, h1, Type130.uvM, Type130.tM, Type130.uvA, Type130.ρM, Type130.uM, uMat,
      Type330.uvM, Type330.tM, Type330.uvA, Type330.ρM, Type330.uM, ofCols_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, -mul_eq_zero,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    first
    | linear_combination (-96) * hG
    | linear_combination (192*J' - 96) * hG
    | ring1

theorem t330_dbl_t130_ρM {m : ℕ} {i F G N i' F' G' N' K' J' : ℤ}
    (h : Type32x.Data m i F G N) (h' : Type130.Data m i' F' G' N' K' J') :
    MatEq (Type130.k m) (Type130.ρM * Matrix.diagonal ![1, 2, 2])
      (Matrix.diagonal ![1, 2, 2] * Type330.ρM) := by
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hG, h0, h1⟩ := dbl_data_t130 h h'
  refine MatEq.of_three_pow_witness (k := Type130.k m) 0
    (W := !![0, 0, 0; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type130.k, h0, h1, Type130.uvM, Type130.tM, Type130.uvA, Type130.ρM, Type130.uM, uMat,
      Type330.uvM, Type330.tM, Type330.uvA, Type330.ρM, Type330.uM, ofCols_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, -mul_eq_zero,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring1

end CFSG.CGT.Stroth77
