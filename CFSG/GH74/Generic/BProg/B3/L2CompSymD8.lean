module

public import CFSG.GH74.Generic.S45.LSymFix

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompSymD8

open Matrix CFSG.GH74.Generic.S45

variable {F : Type} [Field F] {m : ℕ}

@[expose] def reflD (k i₀ : Fin m) : Matrix (Fin m) (Fin m) F :=
  Matrix.diagonal (fun i => if i = k ∨ i = i₀ then (-1 : F) else 1)

theorem reflD_mul_self (k i₀ : Fin m) :
    reflD k i₀ * reflD k i₀ = (1 : Matrix (Fin m) (Fin m) F) := by
  rw [reflD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  by_cases h : i = k ∨ i = i₀ <;> simp [h]

theorem det_reflD {k i₀ : Fin m} (hki : k ≠ i₀) :
    (reflD k i₀ : Matrix (Fin m) (Fin m) F).det = 1 := by
  rw [reflD, Matrix.det_diagonal]
  have h := Finset.prod_eq_mul (s := Finset.univ)
    (f := fun i => if i = k ∨ i = i₀ then (-1 : F) else 1) k i₀ hki
    (fun c _ hc => by simp [hc.1, hc.2]) (fun h => absurd (Finset.mem_univ _) h)
    (fun h => absurd (Finset.mem_univ _) h)
  rw [h]
  simp

theorem reflD_diag {k i₀ : Fin m} (d : Fin m → F) :
    reflD k i₀ * Matrix.diagonal d * (reflD k i₀)ᵀ = (Matrix.diagonal d : Matrix (Fin m) (Fin m) F) := by
  rw [reflD, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  by_cases h : i = k ∨ i = i₀ <;> simp [h]

theorem reflD_rot {j k i₀ : Fin m} (hjk : j ≠ k) (hji : j ≠ i₀) {a : F} (ha : a ≠ 0) :
    reflD k i₀ * rotMat j k a * reflD k i₀ = rotMat j k a * rotMat j k a * rotMat j k a := by
  rw [rotMat_mul_self hjk ha, reflD]
  ext i l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_mul]
  by_cases hl : l = Equiv.swap j k i
  · have key : (if i = k ∨ i = i₀ then (-1 : F) else 1) * (if l = k ∨ l = i₀ then (-1 : F) else 1) =
        (if i = j ∨ i = k then (-1 : F) else 1) := by
      by_cases hij : i = j
      · have hl' : l = k := by rw [hl, hij, Equiv.swap_apply_left]
        rw [hl', hij]
        simp [hjk, hji]
      · by_cases hik : i = k
        · have hl' : l = j := by rw [hl, hik, Equiv.swap_apply_right]
          rw [hl', hik]
          simp [hjk, hji]
        · have hl' : l = i := by rw [hl, Equiv.swap_apply_of_ne_of_ne hij hik]
          rw [hl']
          have hR : (if i = j ∨ i = k then (-1 : F) else 1) = 1 := by simp [hij, hik]
          rw [hR]
          split_ifs <;> norm_num
    calc (if i = k ∨ i = i₀ then (-1 : F) else 1) * rotMat j k a i l *
          (if l = k ∨ l = i₀ then (-1 : F) else 1)
        = ((if i = k ∨ i = i₀ then (-1 : F) else 1) * (if l = k ∨ l = i₀ then (-1 : F) else 1)) *
          rotMat j k a i l := by ring
      _ = (if i = j ∨ i = k then (-1 : F) else 1) * rotMat j k a i l := by rw [key]
  · have h0 : rotMat j k a i l = 0 := by simp [rotMat, hl]
    rw [h0]
    simp

theorem exists_isometry_D8 {F : Type} [Field F] [Fintype F] [DecidableEq F] (h2 : (2 : F) ≠ 0)
    {m : ℕ} (hm : 3 ≤ m) (B : Matrix (Fin m) (Fin m) F) (hB : B.IsSymm) (hBdet : IsUnit B.det) :
    ∃ c b : Matrix (Fin m) (Fin m) F, c.det = 1 ∧ c * B * cᵀ = B ∧
      (∀ l : F, c * c ≠ l • (1 : Matrix (Fin m) (Fin m) F)) ∧ c * c * (c * c) = 1 ∧
      b.det = 1 ∧ b * B * bᵀ = B ∧ b * b = 1 ∧ b * c * b = c * c * c := by
  classical
  obtain ⟨P, d, hP, hPd⟩ := exists_congr_diagonal h2 B hB
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [← hPd, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP.ne_zero hBdet.ne_zero) hP.ne_zero
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    rw [Matrix.det_diagonal] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)
  obtain ⟨j, k, hjk, a, ha⟩ := exists_same_square_class hm d hd
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hd j (by simpa using ha)
  obtain ⟨i0, hi0j, hi0k⟩ : ∃ i0 : Fin m, i0 ≠ j ∧ i0 ≠ k := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin m)) ⊆ {j, k} := fun i _ => by
      by_cases hij : i = j
      · simp [hij]
      · simp [hcon i hij]
    have := Finset.card_le_card hsub
    have h2' : ({j, k} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  let R : Matrix (Fin m) (Fin m) F := rotMat j k a
  let D : Matrix (Fin m) (Fin m) F := reflD k i0
  have hR1 : R * Matrix.diagonal d * Rᵀ = Matrix.diagonal d := rotMat_diag hjk ha0 d ha
  have hR2 : R * R = Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) :=
    rotMat_mul_self hjk ha0
  have hRdet : R.det = 1 := det_rotMat hjk ha0
  have hD2 : D * D = 1 := reflD_mul_self k i0
  have hDdet : D.det = 1 := det_reflD (Ne.symm hi0k)
  have hDR : D * R * D = R * R * R := reflD_rot hjk (Ne.symm hi0j) ha0
  have hDd : D * Matrix.diagonal d * Dᵀ = Matrix.diagonal d := reflD_diag d
  let Q : Matrix (Fin m) (Fin m) F := (P⁻¹)ᵀ
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hQP : Q * Pᵀ = 1 := by
    rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have hPQ : Pᵀ * Q = 1 := by
    rw [← Matrix.transpose_mul, hPP', Matrix.transpose_one]
  have hRR : R * R * (R * R) = 1 := by
    rw [hR2, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    by_cases h : i = j ∨ i = k <;> simp [h]
  have hB' : Q * (Pᵀ * B * P) * Qᵀ = B := by
    calc Q * (Pᵀ * B * P) * Qᵀ = (Q * Pᵀ) * B * (P * P⁻¹) := by
          simp only [Q, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = B := by rw [hQP, hPP, Matrix.one_mul, Matrix.mul_one]
  refine ⟨Q * R * Pᵀ, Q * D * Pᵀ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, hRdet, mul_one, ← Matrix.det_mul, hQP, Matrix.det_one]
  · calc Q * R * Pᵀ * B * (Q * R * Pᵀ)ᵀ
        = Q * (R * (Pᵀ * B * P) * Rᵀ) * Qᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Q * (Pᵀ * B * P) * Qᵀ := by rw [hPd, hR1]
      _ = B := hB'
  · intro l hl
    have h1 : Q * R * Pᵀ * (Q * R * Pᵀ) = Q * (R * R) * Pᵀ := by
      calc Q * R * Pᵀ * (Q * R * Pᵀ) = Q * R * (Pᵀ * Q) * R * Pᵀ := by
            simp only [Matrix.mul_assoc]
        _ = Q * (R * R) * Pᵀ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h1, hR2] at hl
    have h2' : Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) =
        l • (1 : Matrix (Fin m) (Fin m) F) := by
      calc Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1)
          = (Pᵀ * Q) * Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) * (Pᵀ * Q) := by
            rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = Pᵀ * (Q * Matrix.diagonal (fun i => if i = j ∨ i = k then (-1 : F) else 1) * Pᵀ) * Q := by
            simp only [Matrix.mul_assoc]
        _ = Pᵀ * (l • (1 : Matrix (Fin m) (Fin m) F)) * Q := by rw [hl]
        _ = l • (Pᵀ * Q) := by
            rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
        _ = l • (1 : Matrix (Fin m) (Fin m) F) := by rw [hPQ]
    have e1 := congrFun (congrFun h2' j) j
    have e2 := congrFun (congrFun h2' i0) i0
    simp [Matrix.diagonal_apply_eq, Matrix.smul_apply, hi0j, hi0k] at e1 e2
    apply h2
    linear_combination e2 - e1
  · have h1 : Q * R * Pᵀ * (Q * R * Pᵀ) = Q * (R * R) * Pᵀ := by
      calc Q * R * Pᵀ * (Q * R * Pᵀ) = Q * R * (Pᵀ * Q) * R * Pᵀ := by
            simp only [Matrix.mul_assoc]
        _ = Q * (R * R) * Pᵀ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [h1]
    calc Q * (R * R) * Pᵀ * (Q * (R * R) * Pᵀ) = Q * (R * R) * (Pᵀ * Q) * (R * R) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hPQ, Matrix.mul_one, show Q * (R * R) * (R * R) * Pᵀ = Q * (R * R * (R * R)) * Pᵀ by
            simp only [Matrix.mul_assoc], hRR, Matrix.mul_one, hQP]
  · rw [Matrix.det_mul, Matrix.det_mul, hDdet, mul_one, ← Matrix.det_mul, hQP, Matrix.det_one]
  · calc Q * D * Pᵀ * B * (Q * D * Pᵀ)ᵀ
        = Q * (D * (Pᵀ * B * P) * Dᵀ) * Qᵀ := by
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = Q * (Pᵀ * B * P) * Qᵀ := by rw [hPd, hDd]
      _ = B := hB'
  · calc Q * D * Pᵀ * (Q * D * Pᵀ) = Q * D * (Pᵀ * Q) * D * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (D * D) * Pᵀ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD2, Matrix.mul_one, hQP]
  · calc Q * D * Pᵀ * (Q * R * Pᵀ) * (Q * D * Pᵀ)
        = Q * (D * R * D) * Pᵀ := by
          calc Q * D * Pᵀ * (Q * R * Pᵀ) * (Q * D * Pᵀ)
              = Q * D * (Pᵀ * Q) * R * (Pᵀ * Q) * D * Pᵀ := by simp only [Matrix.mul_assoc]
            _ = Q * (D * R * D) * Pᵀ := by rw [hPQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Q * (R * R * R) * Pᵀ := by rw [hDR]
      _ = Q * R * Pᵀ * (Q * R * Pᵀ) * (Q * R * Pᵀ) := by
          calc Q * (R * R * R) * Pᵀ
              = Q * R * (Pᵀ * Q) * R * (Pᵀ * Q) * R * Pᵀ := by
                rw [hPQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]

end CFSG.GH74.Generic.BProg.B3.L2CompSymD8
