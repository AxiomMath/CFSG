module

public import CFSG.LinearAlgebra.DesarguesianPlanes.LinearCentralizerData

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {F : Type} [Field F]

theorem fin_two_mul_self (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = N.trace • N - N.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem sub_one_mul_self_eq_zero (p : ℕ) [hp : Fact p.Prime] [CharP F p] (A : GL (Fin 2) F)
    (hA : A ^ p = 1) :
    ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
  set N := (A : Matrix (Fin 2) (Fin 2) F) - 1 with hN
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute p (Commute.one_right _), one_pow,
      ← Units.val_pow_eq_pow_val, hA, Units.val_one, sub_self]
  have hdet : N.det = 0 := by
    have h := congrArg Matrix.det hNp
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact (pow_eq_zero_iff hp.out.ne_zero).mp h
  have hsq : N * N = N.trace • N := by rw [fin_two_mul_self, hdet, zero_smul, sub_zero]
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, ← pow_succ]
  have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_lt.le).symm
  rw [hp1, hpow] at hNp
  rw [hsq]
  rcases smul_eq_zero.mp hNp with h | h
  · have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
    rw [(pow_eq_zero_iff hp2).mp h, zero_smul]
  · rw [h, smul_zero]

theorem unipotent_entries {A : Matrix (Fin 2) (Fin 2) F} (hA : (A - 1) * (A - 1) = 0) :
    (A 0 0 - 1) * (A 0 0 - 1) + A 0 1 * A 1 0 = 0 ∧
      (A 0 0 - 1) * A 0 1 + A 0 1 * (A 1 1 - 1) = 0 ∧
      A 1 0 * (A 0 0 - 1) + (A 1 1 - 1) * A 1 0 = 0 ∧
      A 1 0 * A 0 1 + (A 1 1 - 1) * (A 1 1 - 1) = 0 := by
  have h00 := congrFun (congrFun hA 0) 0
  have h01 := congrFun (congrFun hA 0) 1
  have h10 := congrFun (congrFun hA 1) 0
  have h11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10,
    by linear_combination h11⟩

theorem inv_mul_mul_eq_of_mul_eq {A P B : GL (Fin 2) F} (h : A * P = P * B) :
    P⁻¹ * A * P = B := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_upperGL_of_unipotent (M : GL (Fin 2) F)
    (hM : ((M : Matrix (Fin 2) (Fin 2) F) - 1) * ((M : Matrix (Fin 2) (Fin 2) F) - 1) = 0)
    (h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    M = upperGL ((M : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  obtain ⟨e00, -, -, e11⟩ := unipotent_entries hM
  rw [h10, mul_zero, add_zero] at e00
  rw [h10, zero_mul, zero_add] at e11
  have h00 := sub_eq_zero.mp (mul_self_eq_zero.mp e00)
  have h11 := sub_eq_zero.mp (mul_self_eq_zero.mp e11)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperGL, h00, h10, h11]

theorem conj_unipotent (A k : GL (Fin 2) F)
    (hA : ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0) :
    (((k⁻¹ * A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1) *
      (((k⁻¹ * A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
  have hk : ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (k : Matrix (Fin 2) (Fin 2) F) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hk' : (k : Matrix (Fin 2) (Fin 2) F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((k⁻¹ * A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) - 1 =
      ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((A : Matrix (Fin 2) (Fin 2) F) - 1) * (k : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, hk]
  rw [h1]
  calc ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) *
        (k : Matrix (Fin 2) (Fin 2) F) *
      (((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((A : Matrix (Fin 2) (Fin 2) F) - 1) * (k : Matrix (Fin 2) (Fin 2) F))
      = ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (((A : Matrix (Fin 2) (Fin 2) F) - 1) *
            ((k : Matrix (Fin 2) (Fin 2) F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
            ((A : Matrix (Fin 2) (Fin 2) F) - 1)) * (k : Matrix (Fin 2) (Fin 2) F) := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hk', Matrix.mul_one, hA, Matrix.mul_zero, Matrix.zero_mul]

theorem conj_lower_left_eq_zero (A k : GL (Fin 2) F)
    (h0 : ((A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (k : Matrix (Fin 2) (Fin 2) F) 0 0)
    (h1 : ((A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      (k : Matrix (Fin 2) (Fin 2) F) 1 0) :
    ((k⁻¹ * A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have hk : ((k⁻¹ * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [inv_mul_cancel, Units.val_one]; simp
  rw [mul_assoc, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, h1]
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at hk
  exact hk

theorem exists_conj_upperGL_mem (h2 : (2 : F) ≠ 0) (A : GL (Fin 2) F)
    (hA : ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0) :
    ∃ k : GL (Fin 2) F, (∃ c : F, k⁻¹ * A * k = upperGL c) ∧
      (k = 1 ∨ k = swapGL ∨ (∃ l : Fˣ, k = diagGL l 1 * A) ∨
        (∃ l : Fˣ, k = diagGL l 1 * A * swapGL)) := by
  obtain ⟨e00, e01, e10, e11⟩ := unipotent_entries hA
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb_def
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc_def
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
  have key : ∀ k : GL (Fin 2) F,
      ((A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (k : Matrix (Fin 2) (Fin 2) F) 0 0 →
      ((A * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 =
        (k : Matrix (Fin 2) (Fin 2) F) 1 0 →
      ∃ c : F, k⁻¹ * A * k = upperGL c := fun k h0 h1 =>
    ⟨_, eq_upperGL_of_unipotent _ (conj_unipotent A k hA) (conj_lower_left_eq_zero A k h0 h1)⟩
  by_cases hb : b = 0
  ·
    have hd1 : d = 1 := by
      rw [hb, mul_zero, zero_add] at e11
      exact sub_eq_zero.mp (mul_self_eq_zero.mp e11)
    have hk : ((swapGL : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapGL]
    refine ⟨swapGL, key _ ?_ ?_, Or.inr (Or.inl rfl)⟩ <;>
      rw [Units.val_mul, hk] <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp only [← hb_def, ← hd_def, hb, hd1]
  by_cases hc : c = 0
  · have ha1 : a = 1 := by
      rw [hc, mul_zero, add_zero] at e00
      exact sub_eq_zero.mp (mul_self_eq_zero.mp e00)
    refine ⟨1, key _ ?_ ?_, Or.inl rfl⟩ <;> rw [mul_one] <;> simp <;>
      simp only [← ha_def, ← hc_def, ha1, hc]
  have hd : d = 2 - a := by
    have : b * (a + d - 2) = 0 := by linear_combination e01
    have := (mul_eq_zero.mp this).resolve_left hb
    linear_combination this
  by_cases ha0 : a = 0
  ·
    have h2u : IsUnit (2 : F) := isUnit_iff_ne_zero.mpr h2
    have hk : ((diagGL h2u.unit 1 * A * swapGL : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![2 * b, 2 * a; d, c] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagGL, swapGL, IsUnit.unit_spec, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, ← ha_def, ← hb_def, ← hc_def, ← hd_def]
    refine ⟨diagGL h2u.unit 1 * A * swapGL, key _ ?_ ?_, Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))⟩
    · rw [Units.val_mul _ (diagGL h2u.unit 1 * A * swapGL), hk]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ]
      simp only [← ha_def, ← hb_def]
      linear_combination b * hd + b * ha0
    · rw [Units.val_mul _ (diagGL h2u.unit 1 * A * swapGL), hk]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ]
      simp only [← hc_def, ← hd_def]
      linear_combination 2 * e00 + (d + 1 - a) * hd + (1 - a) * ha0
  ·
    have ha1 : a - 1 ≠ 0 := by
      intro h
      rw [h, zero_mul, zero_add] at e00
      exact (mul_ne_zero hb hc) e00
    have hl : (a - 1) / a ≠ 0 := div_ne_zero ha1 ha0
    set l := (a - 1) / a with hl_def
    have hla : l * a = a - 1 := div_mul_cancel₀ _ ha0
    have hk : ((diagGL (Units.mk0 l hl) 1 * A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        !![l * a, l * b; c, d] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagGL, Matrix.mul_apply, Fin.sum_univ_two, ← ha_def, ← hb_def, ← hc_def,
          ← hd_def]
    refine ⟨diagGL (Units.mk0 l hl) 1 * A, key _ ?_ ?_, Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))⟩
    · rw [Units.val_mul _ (diagGL (Units.mk0 l hl) 1 * A), hk]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ]
      simp only [← ha_def, ← hb_def]
      linear_combination e00 + (a - 1) * hla
    · rw [Units.val_mul _ (diagGL (Units.mk0 l hl) 1 * A), hk]
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
        ]
      simp only [← hc_def, ← hd_def]
      linear_combination c * hla + c * hd

theorem exists_conj_upperGL (h2 : (2 : F) ≠ 0) (A : GL (Fin 2) F)
    (hA : ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0) :
    ∃ (P : GL (Fin 2) F) (c : F), P⁻¹ * A * P = upperGL c := by
  obtain ⟨k, ⟨c, hc⟩, -⟩ := exists_conj_upperGL_mem h2 A hA
  exact ⟨k, c, hc⟩

theorem diagGL_one_neg_one_inv :
    (diagGL 1 (-1) : GL (Fin 2) F)⁻¹ = diagGL 1 (-1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [diagGL_mul, mul_one, neg_one_mul, neg_neg, diagGL_one_one]

theorem upper_or_lower_of_diag_conj_eq_inv (h2 : (2 : F) ≠ 0) (A : GL (Fin 2) F)
    (hA : ((A : Matrix (Fin 2) (Fin 2) F) - 1) * ((A : Matrix (Fin 2) (Fin 2) F) - 1) = 0)
    (hinv : diagGL 1 (-1) * A * (diagGL 1 (-1))⁻¹ = A⁻¹) :
    (∃ c : F, A = upperGL c) ∨ (∃ c : F, A = lowerGL c) := by
  obtain ⟨e00, e01, e10, e11⟩ := unipotent_entries hA
  rw [diagGL_one_neg_one_inv] at hinv
  have h1 : diagGL 1 (-1) * A * diagGL 1 (-1) * A = 1 := by rw [hinv, inv_mul_cancel]
  have hm := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) h1
  simp only [Units.val_mul, Units.val_one] at hm
  have E00 := congrFun (congrFun hm 0) 0
  have E11 := congrFun (congrFun hm 1) 1
  simp [diagGL, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at E00 E11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb_def
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc_def
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
  have hsum : 2 * (a * (a - 1)) = 0 := by linear_combination e00 + E00
  have hsum' : 2 * (d * (d - 1)) = 0 := by linear_combination e11 + E11
  have haa := (mul_eq_zero.mp hsum).resolve_left h2
  have hdd := (mul_eq_zero.mp hsum').resolve_left h2
  have ha : a = 1 := by
    rcases mul_eq_zero.mp haa with ha | ha
    · exfalso
      have hbc : b * c = -1 := by rw [ha] at e00; linear_combination e00
      have hb : b ≠ 0 := by
        intro hb
        rw [hb, zero_mul] at hbc
        exact one_ne_zero (neg_eq_zero.mp hbc.symm)
      have hd : a + d - 2 = 0 := by
        have : b * (a + d - 2) = 0 := by linear_combination e01
        exact (mul_eq_zero.mp this).resolve_left hb
      rw [ha] at hd
      have hd2 : d = 2 := by linear_combination hd
      rw [hd2] at hdd
      exact h2 (by linear_combination hdd)
    · exact sub_eq_zero.mp ha
  have hbc : b * c = 0 := by rw [ha] at e00; linear_combination e00
  have hd : d = 1 := by
    have : (d - 1) * (d - 1) = 0 := by linear_combination e11 - hbc
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  rcases mul_eq_zero.mp hbc with hb | hc
  · right
    refine ⟨c, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerGL] <;>
      simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, ha, hb, hd]
  · left
    refine ⟨b, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperGL] <;>
      simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, ha, hc, hd]

theorem exists_conj_diagGL_of_mul_self (h2 : (2 : F) ≠ 0) (A : GL (Fin 2) F) (hA : A * A = 1)
    (h1 : A ≠ 1) (hm1 : A ≠ -1) : ∃ P : GL (Fin 2) F, P⁻¹ * A * P = diagGL 1 (-1) := by
  have hm := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) hA
  simp only [Units.val_mul, Units.val_one] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0 with ha_def
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb_def
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc_def
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd_def
  have hD : ((diagGL 1 (-1) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL]
  have htr : d = -a := by
    by_contra htr
    have hs : a + d ≠ 0 := fun h => htr (by linear_combination h)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have ha : (a - 1) * (a + 1) = 0 := by rw [hb, zero_mul, add_zero] at e00; linear_combination e00
    have hd : (d - 1) * (d + 1) = 0 := by rw [hc, zero_mul, zero_add] at e11; linear_combination e11
    rcases mul_eq_zero.mp ha with ha | ha <;> rcases mul_eq_zero.mp hd with hd | hd
    · apply h1
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;>
        simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, hb, hc] <;>
        first | linear_combination ha | linear_combination hd
    · exact hs (by linear_combination ha + hd)
    · exact hs (by linear_combination ha + hd)
    · apply hm1
      ext i j
      fin_cases i <;> fin_cases j <;> simp <;>
        simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, hb, hc] <;>
        first | linear_combination ha | linear_combination hd
  have hdet : a * a + b * c = 1 := by linear_combination e00
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · have ha : (a - 1) * (a + 1) = 0 := by
        rw [hb, zero_mul, add_zero] at hdet; linear_combination hdet
      rcases mul_eq_zero.mp ha with ha | ha
      · refine ⟨1, ?_⟩
        rw [inv_one, one_mul, mul_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diagGL] <;>
          simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, hb, hc, htr] <;>
          first | linear_combination ha | linear_combination -ha
      · refine ⟨swapGL, inv_mul_mul_eq_of_mul_eq ?_⟩
        have hk : ((swapGL : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [swapGL]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hk, hD]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
          simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def, hb, hc, htr] <;>
          first | linear_combination ha | linear_combination -ha
    ·
      have hP : (!![1 + a, a - 1; c, c] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h
        have : 2 * c = 0 := by linear_combination h
        exact hc ((mul_eq_zero.mp this).resolve_left h2)
      refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hP, inv_mul_mul_eq_of_mul_eq ?_⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hD]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def] <;>
        first | ring1 | linear_combination hdet | linear_combination c * htr
  ·
    have hP : (!![b, b; 1 - a, -1 - a] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      intro h
      have : 2 * b = 0 := by linear_combination -h
      exact hb ((mul_eq_zero.mp this).resolve_left h2)
    refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hP, inv_mul_mul_eq_of_mul_eq ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp only [← ha_def, ← hb_def, ← hc_def, ← hd_def] <;>
      first | ring1 | linear_combination hdet + (1 - a) * htr |
        linear_combination hdet + (-1 - a) * htr

theorem eq_scalar_mul_upperGL_of_commute {c : F} (hc : c ≠ 0) (A : GL (Fin 2) F)
    (hA : A * upperGL c = upperGL c * A) :
    ∃ (a : Fˣ) (b : F), A = Matrix.GeneralLinearGroup.scalar (Fin 2) a * upperGL b := by
  have hm := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F)) hA
  simp only [Units.val_mul] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := e00.resolve_left hc
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    have : c * ((A : Matrix (Fin 2) (Fin 2) F) 1 1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      linear_combination -e01
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc))
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (A.isUnit.map Matrix.detMonoidHom).ne_zero
  rw [Matrix.det_fin_two, h10, h11, mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ ha, (A : Matrix (Fin 2) (Fin 2) F) 0 1 / (A : Matrix (Fin 2) (Fin 2) F) 0 0,
    ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperGL, Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
  field_simp

end CFSG.BrauerLinearThree
