module

public import CFSG.GH74.Generic.BProg.B2.GenLocL5Sign
public import CFSG.GH74.Generic.BProg.B2.GenLocL4OutE16

public section

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

open CFSG CFSG.GH74 Matrix
open scoped MatrixGroups


section NF

variable {F : Type} [Field F]

theorem exists_two_sq [Finite F] (hodd : Nat.card F % 2 = 1) {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (c : F) :
    ∃ x y : F, a * x ^ 2 + b * y ^ 2 = c := by
  classical
  have := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by rwa [← Nat.card_eq_fintype_card]
  open Polynomial in
  have hf : (C a * X ^ 2 : F[X]).degree = 2 := by
    rw [degree_C_mul ha, degree_X_pow]; rfl
  open Polynomial in
  have hg : (C b * X ^ 2 - C c : F[X]).degree = 2 := by
    rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_C_mul hb, degree_X_pow]
    · rfl
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  obtain ⟨x, y, h⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨x, y, ?_⟩
  simp at h
  linear_combination h

end NF

section Plus

variable {F : Type} [Field F]

theorem exists_lam (e1 e2 s : F) (he1 : e1 ≠ 0) (hprod : e1 * e2 = s ^ 2) :
    ∃ l : F, l ^ 2 * e1 = e2 ∧ l * e1 = s := by
  refine ⟨s / e1, ?_, ?_⟩
  · field_simp
    linear_combination (-1 : F) * hprod
  · field_simp

theorem diag_eq_mul_t [Finite F] (hodd : Nat.card F % 2 = 1) (d : Fin 4 → F) (hd : ∀ i, d i ≠ 0) (s : F) (hs : s ≠ 0)
    (hprod : d 0 * d 1 * (d 2 * d 3) = s ^ 2) :
    ∃ P : Matrix (Fin 4) (Fin 4) F, P.det ≠ 0 ∧ Matrix.diagonal d = P * Pᵀ := by
  obtain ⟨x1, y1, h1⟩ := exists_two_sq hodd (hd 0) (hd 1) 1
  obtain ⟨x2, y2, h2⟩ := exists_two_sq hodd (hd 2) (hd 3) 1
  have he1 : d 0 * d 1 ≠ 0 := mul_ne_zero (hd 0) (hd 1)
  obtain ⟨u1, u2, hu⟩ := exists_two_sq hodd (one_ne_zero : (1 : F) ≠ 0) (one_ne_zero : (1 : F) ≠ 0) (d 0 * d 1)
  obtain ⟨l, hl2, hl1⟩ := exists_lam (d 0 * d 1) (d 2 * d 3) s he1 hprod
  set P1 : Matrix (Fin 4) (Fin 4) F :=
    !![d 0 * x1, -y1, 0, 0; d 1 * y1, x1, 0, 0; 0, 0, d 2 * x2, -y2; 0, 0, d 3 * y2, x2] with hP1
  set P2 : Matrix (Fin 4) (Fin 4) F :=
    !![1, 0, 0, 0; 0, u1, 0, u2; 0, 0, 1, 0; 0, -(l * u2), 0, l * u1] with hP2
  set D1 : Matrix (Fin 4) (Fin 4) F := !![1, 0, 0, 0; 0, d 0 * d 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, d 2 * d 3] with hD1
  have hdet1 : P1.det = 1 := by
    simp [hP1, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    linear_combination (d 2 * x2 ^ 2 + d 3 * y2 ^ 2) * h1 + h2
  have hdet2 : P2.det = s := by
    simp [hP2, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    linear_combination l * hu + hl1
  have e1 : P2 * P2ᵀ = D1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP2, hD1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
    · linear_combination hu
    · ring
    · ring
    · linear_combination l ^ 2 * hu + hl2
  have e2 : P1 * D1 * P1ᵀ = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP1, hD1, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
    · linear_combination d 0 * h1
    · ring
    · ring
    · linear_combination d 1 * h1
    · linear_combination d 2 * h2
    · ring
    · ring
    · linear_combination d 3 * h2
  refine ⟨P1 * P2, ?_, ?_⟩
  · rw [Matrix.det_mul, hdet1, hdet2, one_mul]; exact hs
  · rw [Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc P1, e1, e2]

end Plus

section PlusB

variable {F : Type} [Field F]

theorem ringChar_ne_two_of_card_mod [Finite F] (hF4 : Nat.card F % 4 = 3) : ringChar F ≠ 2 := by
  intro h
  have : CharP F 2 := by rw [← h]; exact ringChar.charP F
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  have h2 : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have h3 : 2 ∣ Nat.card F := by rw [h2]; exact dvd_pow_self 2 (by omega)
  omega

theorem exists_cong_plus [Finite F] (hF4 : Nat.card F % 4 = 3) (B : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = B)
    (hdet : B.det ≠ 0) (hsq : IsSquare B.det) :
    ∃ P : GL (Fin 4) F, B = (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by
  have hodd : Nat.card F % 2 = 1 := by omega
  have hK := ringChar_ne_two_of_card_mod hF4
  obtain ⟨Q, hQ⟩ := GenLocL5Sign.exists_orthogonal_congr hK B hBt
  set D : Matrix (Fin 4) (Fin 4) F := (Q : Matrix (Fin 4) (Fin 4) F)ᵀ * B * (Q : Matrix (Fin 4) (Fin 4) F) with hD
  have hDd : D = Matrix.diagonal (fun i => D i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.diagonal_apply_ne _ hij]; exact hQ i j hij
  have hdQ : (Q : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit).ne_zero
  obtain ⟨r, hr⟩ := hsq
  have hdetD : D.det = ((Q : Matrix (Fin 4) (Fin 4) F).det * r) ^ 2 := by
    rw [hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hr]; ring
  have hs : (Q : Matrix (Fin 4) (Fin 4) F).det * r ≠ 0 := by
    intro h0
    have : D.det = 0 := by rw [hdetD, h0]; ring
    rw [hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at this
    have h1 : (Q : Matrix (Fin 4) (Fin 4) F).det * B.det * (Q : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
      mul_ne_zero (mul_ne_zero hdQ hdet) hdQ
    exact h1 this
  have hdD : ∀ i, D i i ≠ 0 := by
    intro i h0
    have : D.det = 0 := by
      rw [hDd, Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    rw [hdetD] at this
    exact hs (pow_eq_zero_iff (two_ne_zero) |>.1 this)
  have hprod : D 0 0 * D 1 1 * (D 2 2 * D 3 3) = ((Q : Matrix (Fin 4) (Fin 4) F).det * r) ^ 2 := by
    rw [← hdetD, hDd, Matrix.det_diagonal, Fin.prod_univ_four]
    simp only [Matrix.diagonal_apply_eq]
    ring
  obtain ⟨P0, hP0, hDP⟩ := diag_eq_mul_t hodd (fun i => D i i) hdD _ hs hprod
  set Qi : Matrix (Fin 4) (Fin 4) F := ((Q⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hQi
  have hQQi : (Q : Matrix (Fin 4) (Fin 4) F) * Qi = 1 := by rw [hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * (Q : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdetQi : Qi.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hQiQ
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hM : (Qiᵀ * P0).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose]; exact mul_ne_zero hdetQi hP0
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (Qiᵀ * P0) hM, ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero (Qiᵀ * P0) hM : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Qiᵀ * P0 := rfl
  rw [hcoe]
  have hBD : B = Qiᵀ * D * Qi := by
    calc B = (Qiᵀ * (Q : Matrix (Fin 4) (Fin 4) F)ᵀ) * B * ((Q : Matrix (Fin 4) (Fin 4) F) * Qi) := by
          rw [← Matrix.transpose_mul, hQQi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
      _ = Qiᵀ * D * Qi := by rw [hD]; simp only [Matrix.mul_assoc]
  rw [hBD, hDd, hDP, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

end PlusB

section Skew

variable {F : Type} [Field F]

theorem cong_of_trans (B N : Matrix (Fin 4) (Fin 4) F) (P : GL (Fin 4) F)
    (h : (P : Matrix (Fin 4) (Fin 4) F)ᵀ * B * (P : Matrix (Fin 4) (Fin 4) F) = N) :
    ∃ Q : GL (Fin 4) F, B = (Q : Matrix (Fin 4) (Fin 4) F) * N * (Q : Matrix (Fin 4) (Fin 4) F)ᵀ := by
  set Pi : Matrix (Fin 4) (Fin 4) F := ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hPi
  have hPPi : (P : Matrix (Fin 4) (Fin 4) F) * Pi = 1 := by rw [hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by rw [hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdPi : Pi.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hPiP
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdQ : (Piᵀ).det ≠ 0 := by rw [Matrix.det_transpose]; exact hdPi
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Piᵀ hdQ, ?_⟩
  have hcoe : ((Matrix.GeneralLinearGroup.mkOfDetNeZero Piᵀ hdQ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Piᵀ := rfl
  rw [hcoe, Matrix.transpose_transpose, ← h]
  calc B = (Piᵀ * (P : Matrix (Fin 4) (Fin 4) F)ᵀ) * B * ((P : Matrix (Fin 4) (Fin 4) F) * Pi) := by
        rw [← Matrix.transpose_mul, hPPi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_cong_skew [Finite F] (hF4 : Nat.card F % 4 = 3) (B : Matrix (Fin 4) (Fin 4) F) (hBt : Bᵀ = -B)
    (hdet : B.det ≠ 0) :
    ∃ P : GL (Fin 4) F, B = (P : Matrix (Fin 4) (Fin 4) F) * m1 * (P : Matrix (Fin 4) (Fin 4) F)ᵀ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two_of_card_mod hF4)
  have hB' : ∀ i j, B j i = -B i j := fun i j => by
    have := congrFun (congrFun hBt i) j
    simpa using this
  let β : LinearMap.BilinForm F (Fin 4 → F) := Matrix.toBilin' B
  have hα : β.IsAlt := by
    intro x
    have h1 : β x x = -β x x := by
      simp only [β, Matrix.toBilin'_apply]
      calc ∑ i, ∑ j, x i * B i j * x j = ∑ i, ∑ j, x j * B j i * x i := Finset.sum_comm
        _ = ∑ i, ∑ j, -(x i * B i j * x j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hB' i j]; ring
        _ = -∑ i, ∑ j, x i * B i j * x j := by simp [Finset.sum_neg_distrib]
    have h3 : (2 : F) * β x x = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h3).resolve_left h2
  have hnd : β.Nondegenerate := by
    simp only [β]
    exact Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_iff_det_ne_zero.2 hdet)
  obtain ⟨m, b, hm, h00, h11, h01⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis β hα hnd
  have hm2 : m = 2 := by
    have : Module.finrank F (Fin 4 → F) = 4 := by simp
    omega
  subst hm2
  let b' : Module.Basis (Fin 4) F (Fin 4 → F) := b.reindex finSumFinEquiv
  have hb0 : b' 0 = b (Sum.inl 0) := by simp [b']; rfl
  have hb1 : b' 1 = b (Sum.inl 1) := by simp [b']; rfl
  have hb2 : b' 2 = b (Sum.inr 0) := by simp [b']; rfl
  have hb3 : b' 3 = b (Sum.inr 1) := by simp [b']; rfl
  set P : Matrix (Fin 4) (Fin 4) F := (Pi.basisFun F (Fin 4)).toMatrix b' with hP
  have hPik : ∀ i k, P i k = b' k i := fun i k => by simp [hP, Module.Basis.toMatrix_apply]
  have hinv : Invertible P := Module.Basis.invertibleToMatrix _ _
  have hdetP : IsUnit P.det := isUnit_det_of_invertible P
  have hGram : ∀ k l, (Pᵀ * B * P) k l = β (b' k) (b' l) := by
    intro k l
    simp only [β, Matrix.toBilin'_apply, Matrix.mul_apply, Matrix.transpose_apply, hPik, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hs : ∀ x y, β y x = -β x y := fun x y => by
    simp only [β, Matrix.toBilin'_apply]
    calc ∑ i, ∑ j, y i * B i j * x j = ∑ j, ∑ i, y i * B i j * x j := Finset.sum_comm
      _ = ∑ i, ∑ j, -(x i * B i j * y j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hB' i j]; ring
      _ = -∑ i, ∑ j, x i * B i j * y j := by simp [Finset.sum_neg_distrib]
  have e00 : β (b (Sum.inl 0)) (b (Sum.inr 0)) = 1 := by simpa using h01 0 0
  have e01 : β (b (Sum.inl 0)) (b (Sum.inr 1)) = 0 := by simpa using h01 0 1
  have e10 : β (b (Sum.inl 1)) (b (Sum.inr 0)) = 0 := by simpa using h01 1 0
  have e11 : β (b (Sum.inl 1)) (b (Sum.inr 1)) = 1 := by simpa using h01 1 1
  have hG : Pᵀ * B * P = m1 := by
    ext k l
    rw [hGram]
    fin_cases k <;> fin_cases l <;> simp [m1, hb0, hb1, hb2, hb3]
    · exact h00 0 0
    · exact h00 0 1
    · exact e00
    · exact e01
    · exact h00 1 0
    · exact h00 1 1
    · exact e10
    · exact e11
    · rw [hs, e00]
    · rw [hs, e10]; simp
    · exact h11 0 0
    · exact h11 0 1
    · rw [hs, e01]; simp
    · rw [hs, e11]
    · exact h11 1 0
    · exact h11 1 1
  obtain ⟨u, hu⟩ := hdetP
  have hdetne : P.det ≠ 0 := by rw [← hu]; exact u.ne_zero
  obtain ⟨Q, hQ⟩ := cong_of_trans B m1 (Matrix.GeneralLinearGroup.mkOfDetNeZero P hdetne) hG
  exact ⟨Q, hQ⟩

end Skew


end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
