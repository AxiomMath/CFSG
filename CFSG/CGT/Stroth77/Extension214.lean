module

public import CFSG.CGT.Stroth77.Extension212Group4
public import CFSG.CGT.Stroth77.Extension219

public section

namespace CFSG.CGT.Stroth77

open Matrix

theorem GV_succ_eq_t320 {m : ℕ} (hm : 1 ≤ m) :
    Type120.GV (m + 1) = Type120.GV m + 2 ^ (m - 1) * 2 ^ (m - 1) := by
  have h1 := Type120.three_mul_GV (m + 1)
  have h3 := Type120.three_mul_GV m
  rw [Nat.add_sub_cancel] at h1
  have h4 : (4 : ℤ) ^ m = 4 * (2 ^ (m - 1) * 2 ^ (m - 1)) := by
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, ← mul_pow, pow_succ]
    norm_num
    ring
  have h4' : (4 : ℤ) ^ (m - 1) = 2 ^ (m - 1) * 2 ^ (m - 1) := by
    rw [← mul_pow]; norm_num
  linarith

theorem t320_uvM_restr {m : ℕ} (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t120 m hm).k
      ((StrothTypeIndex.t120 m hm).action.uv * diag4)
      (diag4 * (StrothTypeIndex.t320 m hm).action.uv) := by
  change MatEq (Type120.k m)
    (Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) * _)
    (_ * Type320.uvM (Type120.iV m) (Type120.FV m) (Type120.GV m))
  obtain ⟨hi1, hF1, -⟩ := Type120.data m (by omega)
  obtain ⟨-, hi3, hF3, hG3, -⟩ := Type32x.data m (by omega)
  have hG1 := GV_succ_eq_t320 (m := m) (by omega)
  have h2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2m1 : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := by rw [pow_succ, h2m]; ring
  generalize Type120.iV (m + 1) = i1 at hi1 ⊢
  generalize Type120.FV (m + 1) = F1 at hF1 ⊢
  generalize Type120.iV m = i3 at hi3 ⊢
  generalize Type120.FV m = F3 at hF3 ⊢
  generalize Type120.GV (m + 1) = G1 at hi1 hF1 hG1 ⊢
  generalize Type120.GV m = G at hi3 hF3 hG1 hG3 ⊢
  generalize (2 : ℤ) ^ (m - 1) = N at hG1 hG3 h2m h2m1
  subst hi1 hF1 hi3 hF3 hG1
  refine MatEq.of_three_pow_witness 1 (W := !![-12*N, 320*N^3 - 8*N,
    -5376*N^5 - 6080*N^3 - 196*N; 0, -60*N, -4800*N^3 - 192*N; 0, 24*N, 480*N^3 + 48*N]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, Type320.uvM, Type320.uvA,
      Type320.tM, Type320.ρM, ofCols_apply, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_apply, Fin.sum_univ_three, Type120.k,
      h2m, h2m1] <;>
    first
    | ring1
    | linear_combination (256*N^2) * hG3
    | linear_combination (-6144*N^4 - 4608*G*N^2 - 15616*N^2) * hG3
    | linear_combination (-7680*N^2) * hG3
    | linear_combination (768*N^2) * hG3

theorem t320_tM_restr {m : ℕ} (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t120 m hm).k
      ((StrothTypeIndex.t120 m hm).action.t * diag4)
      (diag4 * (StrothTypeIndex.t320 m hm).action.t) := by
  change MatEq (Type120.k m)
    (Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) * _)
    (_ * Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m))
  obtain ⟨hi1, hF1, -⟩ := Type120.data m (by omega)
  obtain ⟨-, hi3, hF3, hG3, -⟩ := Type32x.data m (by omega)
  have hG1 := GV_succ_eq_t320 (m := m) (by omega)
  have h2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2m1 : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := by rw [pow_succ, h2m]; ring
  generalize Type120.iV (m + 1) = i1 at hi1 ⊢
  generalize Type120.FV (m + 1) = F1 at hF1 ⊢
  generalize Type120.iV m = i3 at hi3 ⊢
  generalize Type120.FV m = F3 at hF3 ⊢
  generalize Type120.GV (m + 1) = G1 at hi1 hF1 hG1 ⊢
  generalize Type120.GV m = G at hi3 hF3 hG1 hG3 ⊢
  generalize (2 : ℤ) ^ (m - 1) = N at hG1 hG3 h2m h2m1
  subst hi1 hF1 hi3 hF3 hG1
  refine MatEq.of_three_pow_witness 1 (W := !![-12*N, 160*N^3 - 220*N, 320*N^3 - 104*N;
    0, -84*N, -24*N; 0, -96*N, -84*N]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.uvA, Type120.tM, Type120.ρM, Type320.uvA, Type320.tM, Type320.ρM,
      ofCols_apply, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_apply, Fin.sum_univ_three, Type120.k, h2m, h2m1] <;>
    first
    | ring1
    | linear_combination (128*N^2) * hG3
    | linear_combination (256*N^2) * hG3

theorem t320_uM_restr {m : ℕ} (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t120 m hm).k
      ((StrothTypeIndex.t120 m hm).action.u * diag4)
      (diag4 * (StrothTypeIndex.t320 m hm).action.u) := by
  change MatEq (Type120.k m) (Type120.uM (Type120.FV (m + 1)) * _)
    (_ * Type320.uM (Type120.FV m))
  obtain ⟨-, hF1, -⟩ := Type120.data m (by omega)
  obtain ⟨-, -, hF3, -, -⟩ := Type32x.data m (by omega)
  have hG1 := GV_succ_eq_t320 (m := m) (by omega)
  have h2m : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h2m1 : (2 : ℤ) ^ (m + 1) = 4 * 2 ^ (m - 1) := by rw [pow_succ, h2m]; ring
  generalize Type120.FV (m + 1) = F1 at hF1 ⊢
  generalize Type120.FV m = F3 at hF3 ⊢
  generalize Type120.GV (m + 1) = G1 at hF1 hG1 ⊢
  generalize Type120.GV m = G at hF3 hG1 ⊢
  generalize (2 : ℤ) ^ (m - 1) = N at hG1 h2m h2m1
  subst hF1 hF3 hG1
  refine MatEq.of_witness (W := !![0, -16*N, -16*N; 0, 0, 0; 0, 0, 0]) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.uM, Type320.uM, uMat, ofCols_apply, diag4, Matrix.mul_diagonal,
      Matrix.diagonal_mul,
      Matrix.mul_apply, Fin.sum_univ_three,
      Type120.k, h2m, h2m1] <;>
    ring1

theorem t320_ρM_restr {m : ℕ} (hm : 3 ≤ m) :
    MatEq (StrothTypeIndex.t120 m hm).k
      ((StrothTypeIndex.t120 m hm).action.ρ * diag4)
      (diag4 * (StrothTypeIndex.t320 m hm).action.ρ) := by
  change MatEq (Type120.k m) (Type120.ρM * _) (_ * Type320.ρM)
  refine MatEq.of_witness (W := 0) ?_
  intro r c
  fin_cases r <;> fin_cases c <;>
    simp [Type120.ρM, Type320.ρM, ofCols_apply, diag4, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem t320_k_pos {m : ℕ} (hm : 3 ≤ m) (i : Fin 3) : 1 ≤ (StrothTypeIndex.t320 m hm).k i := by
  fin_cases i <;> simp [StrothTypeIndex.k, Type32x.k] <;> omega

theorem t320_mats {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t320 m hm).action.uv =
        Type320.uvM (Type120.iV m) (Type120.FV m) (Type120.GV m) ∧
      (StrothTypeIndex.t320 m hm).action.t =
        Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) ∧
      (StrothTypeIndex.t320 m hm).action.u = Type320.uM (Type120.FV m) ∧
      (StrothTypeIndex.t320 m hm).action.ρ = Type320.ρM :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem exists_two_nsmul_ofInt_iff_t320 {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) (v : Fin 3 → ℤ) :
    (∃ z : Torus k, 2 • z = Torus.ofInt k v) ↔ ∀ i, Even (v i) := by
  rw [← Torus.exists_two_zsmul_eq_iff hk]
  simp only [two_nsmul, two_zsmul]

theorem dvd_four_of_exists_four_nsmul_t320 {k : Fin 3 → ℕ} (hk : ∀ i, 2 ≤ k i)
    {v : Fin 3 → ℤ} (h : ∃ z : Torus k, 4 • z = Torus.ofInt k v) (i : Fin 3) : 4 ∣ v i := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨u, rfl⟩ := Torus.exists_ofInt z
  rw [← natCast_zsmul, ← Torus.ofInt_zsmul, Torus.ofInt_eq_ofInt_iff] at hz
  have h4 : (4 : ℤ) ∣ 2 ^ k i := by
    obtain ⟨r, hr⟩ : ∃ r, k i = r + 2 := ⟨k i - 2, by have := hk i; omega⟩
    rw [hr, pow_add]
    exact Dvd.intro_left _ rfl
  have := (hz i).dvd
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_ofNat] at this
  have h' := dvd_trans h4 this
  have h'' : (4 : ℤ) ∣ v i - 4 * u i + 4 * u i := dvd_add h' (dvd_mul_right 4 (u i))
  simpa using h''

theorem parityTorus_rho_t320 {m : ℕ} (hm : 3 ≤ m) (y : Torus (StrothTypeIndex.t320 m hm).k) :
    parityTorus _ (t320_k_pos hm) ((StrothTypeIndex.t320 m hm).action.φρ y) =
      rhoBar300 (parityTorus _ (t320_k_pos hm) y) := by
  obtain ⟨v, rfl⟩ := Torus.exists_ofInt y
  rw [SigmaFourAction.φρ, matAct_ofInt, (t320_mats hm).2.2.2, Torus.ofInt_eq_zsmul_gens,
    Torus.ofInt_eq_zsmul_gens, parityTorus_zsmul_gens, parityTorus_zsmul_gens]
  have h4 : (4 : ZMod 2) = 0 := by decide
  funext r
  fin_cases r <;> simp [rhoBar300, Type320.ρM, ofCols_mulVec, h4, sub_eq_add_neg,
    ZMod.neg_eq_self_mod_two]

theorem t320_rho_a {m : ℕ} (hm : 3 ≤ m) :
    (StrothTypeIndex.t320 m hm).action.φρ (gen (StrothTypeIndex.t320 m hm).k 1) =
      gen (StrothTypeIndex.t320 m hm).k 2 := by
  have h1 : gen (StrothTypeIndex.t320 m hm).k 1 =
      Torus.ofInt (StrothTypeIndex.t320 m hm).k ![0, 1, 0] := by
    rw [Torus.ofInt_eq_zsmul_gens]; simp
  have h2 : gen (StrothTypeIndex.t320 m hm).k 2 =
      Torus.ofInt (StrothTypeIndex.t320 m hm).k ![0, 0, 1] := by
    rw [Torus.ofInt_eq_zsmul_gens]; simp
  rw [h1, h2, SigmaFourAction.φρ, matAct_ofInt, (t320_mats hm).2.2.2]
  congr 1
  funext r
  fin_cases r <;> simp [Type320.ρM, ofCols_mulVec]

theorem t320_fixed_mod_two {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t320 m hm).k)
    (huv : ∃ z, 2 • z = (StrothTypeIndex.t320 m hm).action.φuv v - v)
    (_ht : ∃ z, 2 • z = (StrothTypeIndex.t320 m hm).action.φt v - v)
    (_hu : ∃ z, 2 • z = (StrothTypeIndex.t320 m hm).action.φu v - v)
    (hρ : ∃ z, 2 • z = (StrothTypeIndex.t320 m hm).action.φρ v - v) :
    ∃ z, 2 • z = v := by
  obtain ⟨w, rfl⟩ := Torus.exists_ofInt v
  rw [SigmaFourAction.φuv, matAct_ofInt, ← Torus.ofInt_sub,
    exists_two_nsmul_ofInt_iff_t320 (t320_k_pos hm), (t320_mats hm).1] at huv
  rw [SigmaFourAction.φρ, matAct_ofInt, ← Torus.ofInt_sub,
    exists_two_nsmul_ofInt_iff_t320 (t320_k_pos hm), (t320_mats hm).2.2.2] at hρ
  rw [exists_two_nsmul_ofInt_iff_t320 (t320_k_pos hm)]
  have hρ1 := hρ 1
  have hρ2 := hρ 2
  have huv1 := huv 1
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at hρ1 hρ2 huv1
  have e10 : Type320.uvM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 0 = 1 := by
    simp [Type320.uvM, ofCols_apply]
  have e11 : Type320.uvM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 1 =
      -5 * Type120.iV m := by
    simp [Type320.uvM, Type320.uvA, ofCols_apply]
  rw [e10, e11] at huv1
  simp [Type320.ρM, ofCols_apply] at hρ1 hρ2
  have hw1 : Even (w 1) := by
    rw [even_iff_two_dvd] at hρ1 hρ2 ⊢
    omega
  have hw2 : Even (w 2) := by
    rw [even_iff_two_dvd] at hρ1 hρ2 ⊢
    omega
  intro r
  fin_cases r
  · show Even (w 0)
    have hi' : Type120.iV m = 8 * Type120.GV m + 19 := (Type32x.data m (by omega)).hi
    generalize Type320.uvM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 2 = X at huv1
    obtain ⟨q1, hq1⟩ := hw1
    obtain ⟨q2, hq2⟩ := hw2
    rw [hq1, hq2, hi'] at huv1
    rw [even_iff_two_dvd] at huv1 ⊢
    have : w 0 = (1 * w 0 + -5 * (8 * Type120.GV m + 19) * (q1 + q1) + X * (q2 + q2) -
        (q1 + q1)) - 2 * ((-40 * Type120.GV m - 96) * q1 + X * q2) := by ring
    rw [this]
    exact dvd_sub huv1 (dvd_mul_right 2 _)
  · exact hw1
  · exact hw2

theorem t320_fixed_rho_t {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t320 m hm).k)
    (hρ : (StrothTypeIndex.t320 m hm).action.φρ v = v)
    (ht : (StrothTypeIndex.t320 m hm).action.φt v = v) : v = 0 := by
  obtain ⟨w, rfl⟩ := Torus.exists_ofInt v
  rw [SigmaFourAction.φρ, matAct_ofInt, (t320_mats hm).2.2.2, Torus.ofInt_eq_ofInt_iff] at hρ
  rw [SigmaFourAction.φt, matAct_ofInt, (t320_mats hm).2.1, Torus.ofInt_eq_ofInt_iff] at ht
  have h1 := (hρ 1).dvd
  have h2 := (hρ 2).dvd
  have h3 := (ht 1).dvd
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2 h3
  have e10 : Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 0 = 1 := by
    simp [Type320.tM, ofCols_apply]
  rw [e10] at h3
  generalize Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 1 = X at h3
  generalize Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 2 = Y at h3
  have hk : ∀ i, (StrothTypeIndex.t320 m hm).k i = m := by intro i; fin_cases i <;> rfl
  simp only [hk] at h1 h2 h3
  simp [Type320.ρM, ofCols_apply] at h1 h2
  have hw2 : (2 : ℤ) ^ m ∣ w 2 := by
    have h3w : 3 ^ 1 * w 2 ≡ 3 ^ 1 * 0 [ZMOD 2 ^ m] := by
      rw [Int.modEq_comm, Int.modEq_iff_dvd]
      have := dvd_add h1 h2
      convert this using 1
      ring
    simpa using (int_modEq_of_mul_three_pow 1 m h3w).symm.dvd
  have hw1 : (2 : ℤ) ^ m ∣ w 1 := by
    have := dvd_sub h1 hw2
    convert this using 1
    ring
  have hw0 : (2 : ℤ) ^ m ∣ w 0 := by
    have := dvd_sub (dvd_sub (dvd_sub hw1 (dvd_mul_of_dvd_right hw1 X))
      (dvd_mul_of_dvd_right hw2 Y)) h3
    convert this using 1
    ring
  rw [Torus.ofInt_eq_zero_iff]
  intro r
  fin_cases r <;> simpa [StrothTypeIndex.k, Type32x.k]

theorem t320_fixed_rho_t_mod_four {m : ℕ} (hm : 3 ≤ m) (v : Torus (StrothTypeIndex.t320 m hm).k)
    (hρ : ∃ z, 4 • z = (StrothTypeIndex.t320 m hm).action.φρ v - v)
    (ht : ∃ z, 4 • z = (StrothTypeIndex.t320 m hm).action.φt v - v) :
    ∃ z, 2 • z = v := by
  have hk2 : ∀ i, 2 ≤ (StrothTypeIndex.t320 m hm).k i := by
    intro i; fin_cases i <;> simp [StrothTypeIndex.k, Type32x.k] <;> omega
  obtain ⟨w, rfl⟩ := Torus.exists_ofInt v
  rw [SigmaFourAction.φρ, matAct_ofInt, ← Torus.ofInt_sub, (t320_mats hm).2.2.2] at hρ
  rw [SigmaFourAction.φt, matAct_ofInt, ← Torus.ofInt_sub, (t320_mats hm).2.1] at ht
  have h1 := dvd_four_of_exists_four_nsmul_t320 hk2 hρ 1
  have h2 := dvd_four_of_exists_four_nsmul_t320 hk2 hρ 2
  have h3 := dvd_four_of_exists_four_nsmul_t320 hk2 ht 1
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h1 h2 h3
  have e10 : Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 0 = 1 := by
    simp [Type320.tM, ofCols_apply]
  rw [e10] at h3
  generalize Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 1 = X at h3
  generalize Type320.tM (Type120.iV m) (Type120.FV m) (Type120.GV m) 1 2 = Y at h3
  simp [Type320.ρM, ofCols_apply] at h1 h2
  have hw2 : (4 : ℤ) ∣ w 2 := by omega
  have hw1 : (4 : ℤ) ∣ w 1 := by omega
  have hw0 : (4 : ℤ) ∣ w 0 := by
    have := dvd_sub (dvd_sub h3 (dvd_add (dvd_mul_of_dvd_right hw1 X)
      (dvd_mul_of_dvd_right hw2 Y))) (dvd_neg.mpr hw1)
    convert this using 1
    ring
  rw [exists_two_nsmul_ofInt_iff_t320 (t320_k_pos hm)]
  intro r
  rw [even_iff_two_dvd]
  fin_cases r
  · exact dvd_trans (by norm_num) hw0
  · exact dvd_trans (by norm_num) hw1
  · exact dvd_trans (by norm_num) hw2

theorem exists_two_pow_t120 (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℤ, (2 : ℤ) ^ (m - 1) = N ∧ (2 : ℤ) ^ m = 2 * N ∧ (2 : ℤ) ^ (m + 1) = 4 * N := by
  refine ⟨2 ^ (m - 1), rfl, ?_, ?_⟩
  · rw [← pow_succ']; congr 1; omega
  · rw [show m + 1 = (m - 1) + 2 by omega, pow_add]; ring

theorem profile4_t120_aux {m : ℕ} (hm : 1 ≤ m) {i F G : ℤ} (h : Type120.Data m i F G) :
    Profile4 (Type120.k m) (Type120.action h).φuv (Type120.action h).φt (Type120.action h).φu
      (Type120.action h).φρ := by
  have hi := h.hi
  have hF := h.hF
  subst hi hF
  obtain ⟨N, hN, h2m, h2m1⟩ := exists_two_pow_t120 m hm
  have huv : (Type120.action h).uv = Type120.uvM (8 * G + 19) (4 * G + 9) G := rfl
  have ht : (Type120.action h).t = Type120.tM (8 * G + 19) (4 * G + 9) G := rfl
  have hu : (Type120.action h).u = Type120.uM (4 * G + 9) := rfl
  have hρ : (Type120.action h).ρ = Type120.ρM := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z
    rw [tw_eq_ofInt, tw_eq_ofInt, SigmaFourAction.φuv, matAct_ofInt, huv,
      Torus.ofInt_eq_ofInt_iff]
    intro r
    rw [Int.modEq_iff_dvd]
    fin_cases r <;>
      simp [Type120.k, Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_mulVec, hN,
        h2m, h2m1] <;>
      first
      | exact ⟨768*G^3*z - 64*G^2*y + 6592*G^2*z + 4*G*x - 296*G*y + 18284*G*z + 10*x
          - 342*y + 16530*z, by ring1⟩
      | exact ⟨960*G^2*z + 20*G*y + 4544*G*z + 48*y + 5377*z, by ring1⟩
      | exact ⟨-96*G^2*z - 8*G*y - 464*G*z + x - 19*y - 560*z, by ring1⟩
  · intro x y z
    rw [tw_eq_ofInt, tw_eq_ofInt, SigmaFourAction.φt, matAct_ofInt, ht,
      Torus.ofInt_eq_ofInt_iff]
    intro r
    rw [Int.modEq_iff_dvd]
    fin_cases r <;>
      simp [Type120.k, Type120.uvA, Type120.tM, Type120.ρM, ofCols_mulVec, hN, h2m, h2m1] <;>
      first
      | exact ⟨-32*G^2*y - 64*G^2*z + 4*G*x - 76*G*y - 264*G*z + 8*x - 266*z, by ring1⟩
      | exact ⟨28*G*y + 8*G*z + 67*y + 19*z, by ring1⟩
      | exact ⟨32*G*y + 28*G*z - x + 76*y + 67*z, by ring1⟩
  · intro x y z
    rw [tw_eq_ofInt, tw_eq_ofInt, SigmaFourAction.φu, matAct_ofInt, hu,
      Torus.ofInt_eq_ofInt_iff]
    intro r
    rw [Int.modEq_iff_dvd]
    fin_cases r <;>
      simp [Type120.k, Type120.uM, uMat, ofCols_mulVec, hN, h2m, h2m1] <;>
      first
      | exact ⟨16*G*y + 16*G*z + x + 36*y + 36*z, by ring1⟩
      | exact ⟨0, by ring1⟩
  · intro x y z
    rw [tw_eq_ofInt, tw_eq_ofInt, SigmaFourAction.φρ, matAct_ofInt, hρ,
      Torus.ofInt_eq_ofInt_iff]
    intro r
    rw [Int.modEq_iff_dvd]
    fin_cases r <;>
      simp [Type120.k, Type120.ρM, ofCols_mulVec, hN, h2m, h2m1] <;>
      first
      | exact ⟨2 * z, by ring1⟩
      | exact ⟨z, by ring1⟩
  · refine ⟨-8 * G - 19, 1, -1, ?_⟩
    rw [SigmaFourAction.φuv]
    refine matAct_gen_of _ _ 0 _ _ _ ?_ ?_ ?_ <;> rw [huv] <;>
      simp [Type120.uvM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨64 * G ^ 2 + 296 * G + 342, -20 * G - 48, 8 * G + 19, ?_⟩
    rw [SigmaFourAction.φuv]
    refine matAct_gen_of _ _ 1 _ _ _ ?_ ?_ ?_ <;> rw [huv] <;>
      simp [Type120.uvM, Type120.uvA, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-768 * G ^ 3 - 6592 * G ^ 2 - 18284 * G - 16530, -960 * G ^ 2 - 4544 * G - 5377,
      96 * G ^ 2 + 464 * G + 560, ?_⟩
    rw [SigmaFourAction.φuv]
    refine matAct_gen_of _ _ 2 _ _ _ ?_ ?_ ?_ <;> rw [huv] <;>
      simp [Type120.uvM, Type120.uvA, Type120.tM, Type120.ρM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-8 * G - 15, 1, 2, ?_⟩
    rw [SigmaFourAction.φt]
    refine matAct_gen_of _ _ 0 _ _ _ ?_ ?_ ?_ <;> rw [ht] <;>
      simp [Type120.tM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨32 * G ^ 2 + 76 * G, -28 * G - 67, -32 * G - 76, ?_⟩
    rw [SigmaFourAction.φt]
    refine matAct_gen_of _ _ 1 _ _ _ ?_ ?_ ?_ <;> rw [ht] <;>
      simp [Type120.tM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨64 * G ^ 2 + 264 * G + 266, -8 * G - 19, -28 * G - 67, ?_⟩
    rw [SigmaFourAction.φt]
    refine matAct_gen_of _ _ 2 _ _ _ ?_ ?_ ?_ <;> rw [ht] <;>
      simp [Type120.tM, Type120.uvA, Type120.ρM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-1, 0, 0, ?_⟩
    rw [SigmaFourAction.φu]
    refine matAct_gen_of _ _ 0 _ _ _ ?_ ?_ ?_ <;> rw [hu] <;>
      simp [Type120.uM, uMat, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-16 * G - 36, 0, 0, ?_⟩
    rw [SigmaFourAction.φu]
    refine matAct_gen_of _ _ 1 _ _ _ ?_ ?_ ?_ <;> rw [hu] <;>
      simp [Type120.uM, uMat, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-16 * G - 36, 0, 0, ?_⟩
    rw [SigmaFourAction.φu]
    refine matAct_gen_of _ _ 2 _ _ _ ?_ ?_ ?_ <;> rw [hu] <;>
      simp [Type120.uM, uMat, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨1, 0, 0, ?_⟩
    rw [SigmaFourAction.φρ]
    refine matAct_gen_of _ _ 0 _ _ _ ?_ ?_ ?_ <;> rw [hρ] <;>
      simp [Type120.ρM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨0, 0, 0, ?_⟩
    rw [SigmaFourAction.φρ]
    refine matAct_gen_of _ _ 1 _ _ _ ?_ ?_ ?_ <;> rw [hρ] <;>
      simp [Type120.ρM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1
  · refine ⟨-2, -1, -1, ?_⟩
    rw [SigmaFourAction.φρ]
    refine matAct_gen_of _ _ 2 _ _ _ ?_ ?_ ?_ <;> rw [hρ] <;>
      simp [Type120.ρM, ofCols_apply, ofCols_mulVec,
        -Matrix.mulVec_mulVec] <;> ring1

theorem profile4_t120 {m : ℕ} (hm : 3 ≤ m) :
    Profile4 (StrothTypeIndex.t120 m hm).k (StrothTypeIndex.t120 m hm).action.φuv
      (StrothTypeIndex.t120 m hm).action.φt (StrothTypeIndex.t120 m hm).action.φu
      (StrothTypeIndex.t120 m hm).action.φρ :=
  profile4_t120_aux (by omega) (Type120.data m (by omega))

theorem zsmul_gens_add_t320 {k : Fin 3 → ℕ} (p q r x y z : ℤ) :
    (p • gen k 0 + q • gen k 1 + r • gen k 2) + (x • gen k 0 + y • gen k 1 + z • gen k 2) =
      (p + x) • gen k 0 + (q + y) • gen k 1 + (r + z) • gen k 2 := by
  simp only [add_smul]
  abel

theorem twist4_t121 {m : ℕ} (hm : 3 ≤ m) :
    Twist4 (StrothTypeIndex.t120 m hm).k (StrothTypeIndex.t120 m hm).action.φuv
      (StrothTypeIndex.t120 m hm).action.φt (StrothTypeIndex.t120 m hm).action.φu
      (StrothTypeIndex.t120 m hm).action.φρ (StrothTypeIndex.t121 m hm).action.φuv
      (StrothTypeIndex.t121 m hm).action.φt (StrothTypeIndex.t121 m hm).action.φu
      (StrothTypeIndex.t121 m hm).action.φρ := by
  have h0 := Type120.data m (by omega)
  have h1 := Type121.data m (by omega)
  have cuv : Compat (Type120.k m)
      (Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m)) :=
    Type121.compat_uv h1
  have ct : Compat (Type120.k m)
      (Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m)) :=
    Type121.compat_t h1
  have euv : (StrothTypeIndex.t121 m hm).action.φuv = matAct (Type120.k m)
      (Type121.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m)) cuv :=
    rfl
  have et : (StrothTypeIndex.t121 m hm).action.φt = matAct (Type120.k m)
      (Type121.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)) (2 ^ m)) ct :=
    rfl
  have fuv : (StrothTypeIndex.t120 m hm).action.φuv = matAct (Type120.k m)
      (Type120.uvM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)))
      (Type120.compat_uv h0) := rfl
  have ft : (StrothTypeIndex.t120 m hm).action.φt = matAct (Type120.k m)
      (Type120.tM (Type120.iV (m + 1)) (Type120.FV (m + 1)) (Type120.GV (m + 1)))
      (Type120.compat_t h0) := rfl
  obtain ⟨K, hK, h2m, h2m1⟩ := exists_two_pow_t120 m (by omega)
  have hi := h0.hi
  have hF := h0.hF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · change matAct _ _ cuv (gen (Type120.k m) 0) = matAct _ _ (Type120.compat_uv h0) (gen _ 0)
    rw [matAct_gen_eq, matAct_gen_eq]
    simp [Type121.uvM, Type120.uvM, ofCols_apply]
  · change matAct _ _ cuv (gen (Type120.k m) 1) =
      matAct _ _ (Type120.compat_uv h0) (gen _ 1) + tw (Type120.k m) 0 0 1
    rw [matAct_gen_eq, matAct_gen_eq, tw_eq_ofInt, Torus.ofInt_eq_zsmul_gens,
      zsmul_gens_add_t320]
    apply zsmul_gens_eq_of_dvd <;>
      simp [Type121.uvM, Type121.uvA, Type120.uvM, Type120.uvA, ofCols_apply, Type120.k,
        h2m, h2m1, hK]
  · change matAct _ _ cuv (gen (Type120.k m) 2) =
      matAct _ _ (Type120.compat_uv h0) (gen _ 2) + tw (Type120.k m) 0 1 0
    rw [matAct_gen_eq, matAct_gen_eq, tw_eq_ofInt, Torus.ofInt_eq_zsmul_gens,
      zsmul_gens_add_t320]
    generalize Type120.iV (m + 1) = i at hi ⊢
    generalize Type120.FV (m + 1) = F at hF ⊢
    subst hi hF
    apply zsmul_gens_eq_of_dvd <;>
      simp [Type121.uvM, Type121.uvA, Type121.tM, Type121.ρM, Type120.uvM, Type120.uvA,
        Type120.tM, Type120.ρM, ofCols_apply, ofCols_mulVec, Type120.k, h2m, h2m1, hK,
        -Matrix.mulVec_mulVec] <;>
      first
      | exact ⟨-64 * Type120.GV (m + 1) ^ 2 - 376 * Type120.GV (m + 1) - 532, by ring1⟩
      | exact ⟨-36 * Type120.GV (m + 1) - K - 85, by ring1⟩
      | exact ⟨0, by ring1⟩
  · change matAct _ _ ct (gen (Type120.k m) 0) = matAct _ _ (Type120.compat_t h0) (gen _ 0)
    rw [matAct_gen_eq, matAct_gen_eq]
    simp [Type121.tM, Type120.tM, ofCols_apply]
  · change matAct _ _ ct (gen (Type120.k m) 1) =
      matAct _ _ (Type120.compat_t h0) (gen _ 1) + tw (Type120.k m) 0 1 0
    rw [matAct_gen_eq, matAct_gen_eq, tw_eq_ofInt, Torus.ofInt_eq_zsmul_gens,
      zsmul_gens_add_t320]
    apply zsmul_gens_eq_of_dvd <;>
      simp [Type121.tM, Type120.tM, ofCols_apply, Type120.k, h2m, h2m1, hK]
  · change matAct _ _ ct (gen (Type120.k m) 2) =
      matAct _ _ (Type120.compat_t h0) (gen _ 2) + tw (Type120.k m) 0 1 1
    rw [matAct_gen_eq, matAct_gen_eq, tw_eq_ofInt, Torus.ofInt_eq_zsmul_gens,
      zsmul_gens_add_t320]
    apply zsmul_gens_eq_of_dvd <;>
      simp [Type121.tM, Type121.uvA, Type121.ρM, Type120.tM, Type120.uvA, Type120.ρM,
        ofCols_apply, ofCols_mulVec, Type120.k, h2m, h2m1, hK, -Matrix.mulVec_mulVec] <;>
      first
      | exact ⟨2, by ring1⟩
      | exact ⟨1, by ring1⟩

section Lemma214

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S}

theorem false_of_index_two_t320_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t320 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 2 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') : False :=
  false_of_index_two_of_data D hBC hC hrel hL hH hcS (t320_fixed_mod_two hm)

theorem hasStrothTypeOver_t120_or_t121_of_data {m : ℕ} {hm : 3 ≤ m}
    (D : StrothTypeData B (StrothTypeIndex.t320 m hm)) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B)
    (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t120 m hm) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t121 m hm) := by
  rcases hasStrothTypeOver_or_of_index_four_of_data D hBC hC hrel hL hH hcS (t320_k_pos hm)
      (parityTorus_rho_t320 hm) (t320_rho_a hm) (t320_fixed_rho_t hm)
      (t320_fixed_rho_t_mod_four hm) (StrothTypeIndex.t120 m hm) rfl rfl rfl
      (StrothTypeIndex.t121 m hm).action (profile4_t120 hm) (twist4_t121 hm)
      (t320_uvM_restr hm) (t320_tM_restr hm) (t320_uM_restr hm) (t320_ρM_restr hm)
    with h1 | ⟨E, φ, h2⟩
  · exact Or.inl h1
  · exact Or.inr (hasStrothTypeOver_of_basisChange D hL (StrothTypeIndex.t121 m hm) E φ h2)

theorem hasStrothTypeOver_t120_or_t121_of_data_t321 (D : StrothTypeData B StrothTypeIndex.t321)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t120 3 le_rfl) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t121 3 le_rfl) :=
  (hasStrothTypeOver_t120_or_t121_of_data D.t320OfT321 hBC hC hrel hL hH hcS).imp
    (·.of_gen_eq rfl rfl rfl rfl) (·.of_gen_eq rfl rfl rfl rfl)

end Lemma214

end CFSG.CGT.Stroth77
