module

public import CFSG.CGT.PushingUpLit.A78L3.Heis
public import CFSG.CGT.PushingUpLit.T2K.Nat

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.CGT.PushingUpLit.A78L3 Matrix

section Basis

variable {F : Type} [Field F]

theorem exists_SL2_basis {w y : Fin 2 → F} (hd : det2 w y = 1) (a b c d : F)
    (hdet : a * d - b * c = 1) :
    ∃ M : SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ w = a • w + c • y ∧
      (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = b • w + d • y := by
  let Mat : Matrix (Fin 2) (Fin 2) F := Matrix.of fun i k =>
    (a * det2 (Pi.single k 1) y + b * det2 w (Pi.single k 1)) * w i +
      (c * det2 (Pi.single k 1) y + d * det2 w (Pi.single k 1)) * y i
  have hM : ∀ u, Mat *ᵥ u = (a * det2 u y + b * det2 w u) • w +
      (c * det2 u y + d * det2 w u) • y := by
    intro u
    ext i
    fin_cases i <;> simp [Mat, mulVec, dotProduct, Fin.sum_univ_two, det2] <;> ring
  have hMdet : Mat.det = 1 := by
    rw [det_fin_two]
    simp only [det2] at hd
    simp [Mat, det2]
    linear_combination (w 0 * y 1 - w 1 * y 0) ^ 2 * hdet + (w 0 * y 1 - w 1 * y 0 + 1) * hd
  refine ⟨⟨Mat, hMdet⟩, ?_, ?_⟩
  · show Mat *ᵥ w = _
    rw [hM, det2_self, hd]
    simp
  · show Mat *ᵥ y = _
    rw [hM, det2_self, show det2 w y = 1 from hd]
    simp

theorem exists_diag_SL2 {w y : Fin 2 → F} (hd : det2 w y = 1) {t : F} (ht : t ≠ 0) :
    ∃ M : SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ w = t • w ∧
      (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = t⁻¹ • y := by
  obtain ⟨M, h1, h2⟩ := exists_SL2_basis hd t 0 0 t⁻¹ (by rw [mul_inv_cancel₀ ht]; ring)
  exact ⟨M, by rw [h1]; simp, by rw [h2]; simp⟩

theorem exists_swap_SL2 [CharP F 2] {w y : Fin 2 → F} (hd : det2 w y = 1) :
    ∃ M : SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ w = y ∧
      (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = w := by
  obtain ⟨M, h1, h2⟩ := exists_SL2_basis hd 0 1 1 0 (by
    rw [show (0 : F) * 0 - 1 * 1 = -1 by ring]
    exact CharTwo.neg_eq (1 : F))
  exact ⟨M, by rw [h1]; simp, by rw [h2]; simp⟩

theorem eq_basis {w y : Fin 2 → F} (hd : det2 w y = 1) (u : Fin 2 → F) :
    u = det2 u y • w + det2 w u • y := eq_det2_smul hd u

theorem coords_eq_zero {w y : Fin 2 → F} (hd : det2 w y = 1) {a b : F}
    (h : a • w + b • y = 0) : a = 0 ∧ b = 0 := by
  have h1 : det2 (a • w + b • y) y = a := by
    rw [det2_add_left, det2_smul_left, det2_smul_left, det2_self, hd]
    ring
  have h2 : det2 w (a • w + b • y) = b := by
    rw [det2_add_right, det2_smul_right, det2_smul_right, det2_self, hd]
    ring
  rw [h] at h1 h2
  exact ⟨by simpa [det2] using h1.symm, by simpa [det2] using h2.symm⟩

theorem pow_mulVec_of_eigen {M : Matrix (Fin 2) (Fin 2) F} {v : Fin 2 → F} {c : F}
    (h : M *ᵥ v = c • v) (n : ℕ) : (M ^ n) *ᵥ v = c ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ', mul_comm]

theorem det2_mulVec (M : Matrix (Fin 2) (Fin 2) F) (u v : Fin 2 → F) :
    det2 (M *ᵥ u) (M *ᵥ v) = M.det * det2 u v := by
  simp only [det2, mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

theorem SL2_eq_of_basis {w y : Fin 2 → F} (hd : det2 w y = 1) {M M' : SpecialLinearGroup (Fin 2) F}
    (h1 : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ w = (M' : Matrix (Fin 2) (Fin 2) F) *ᵥ w)
    (h2 : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = (M' : Matrix (Fin 2) (Fin 2) F) *ᵥ y) :
    M = M' := by
  refine CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec (fun u => ?_)
  conv_lhs => rw [eq_basis hd u]
  conv_rhs => rw [eq_basis hd u]
  rw [mulVec_add, mulVec_smul, mulVec_smul, h1, h2, mulVec_add, mulVec_smul, mulVec_smul]

end Basis

section DiagFacts

variable {F : Type} [Field F] {w y : Fin 2 → F} {t : F}

theorem diag_apply (hd : det2 w y = 1) {M : Matrix (Fin 2) (Fin 2) F}
    (hMw : M *ᵥ w = t • w) (hMy : M *ᵥ y = t⁻¹ • y) (u : Fin 2 → F) :
    M *ᵥ u = (t * det2 u y) • w + (t⁻¹ * det2 w u) • y := by
  conv_lhs => rw [eq_basis hd u]
  rw [mulVec_add, mulVec_smul, mulVec_smul, hMw, hMy, smul_smul, smul_smul,
    mul_comm (det2 u y) t, mul_comm (det2 w u) t⁻¹]

theorem eq_zero_of_diag_fix (hd : det2 w y = 1) {M : Matrix (Fin 2) (Fin 2) F}
    (hMw : M *ᵥ w = t • w) (hMy : M *ᵥ y = t⁻¹ • y) (ht1 : t ≠ 1)
    {u : Fin 2 → F} (hu : M *ᵥ u = u) : u = 0 := by
  have h2 := diag_apply hd hMw hMy u
  have h1 := eq_basis hd u
  have h3 : ((t - 1) * det2 u y) • w + ((t⁻¹ - 1) * det2 w u) • y = 0 := by
    have e : (t * det2 u y) • w + (t⁻¹ * det2 w u) • y = det2 u y • w + det2 w u • y := by
      rw [← h2, hu, ← h1]
    calc ((t - 1) * det2 u y) • w + ((t⁻¹ - 1) * det2 w u) • y
        = ((t * det2 u y) • w + (t⁻¹ * det2 w u) • y) - (det2 u y • w + det2 w u • y) := by
          module
      _ = 0 := by rw [e, sub_self]
  obtain ⟨h4, h5⟩ := coords_eq_zero hd h3
  have hα0 : det2 u y = 0 := by
    rcases mul_eq_zero.1 h4 with h | h
    · exact absurd (sub_eq_zero.1 h) ht1
    · exact h
  have hβ0 : det2 w u = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (inv_eq_one.1 (sub_eq_zero.1 h)) ht1
    · exact h
  rw [h1, hα0, hβ0]
  simp

theorem det2_eq_zero_of_eigen (hd : det2 w y = 1) {M : Matrix (Fin 2) (Fin 2) F}
    (hMw : M *ᵥ w = t • w) (hMy : M *ᵥ y = t⁻¹ • y) (hne : t⁻¹ - t ≠ 0) {z : Fin 2 → F}
    (hz : M *ᵥ z = t • z) : det2 w z = 0 := by
  have h2 := diag_apply hd hMw hMy z
  have h1 := eq_basis hd z
  have h3 : (0 : F) • w + ((t⁻¹ - t) * det2 w z) • y = 0 := by
    have e : (t * det2 z y) • w + (t⁻¹ * det2 w z) • y = t • z := by rw [← h2, hz]
    conv_rhs at e => rw [h1, smul_add, smul_smul, smul_smul]
    calc (0 : F) • w + ((t⁻¹ - t) * det2 w z) • y
        = ((t * det2 z y) • w + (t⁻¹ * det2 w z) • y) -
          ((t * det2 z y) • w + (t * det2 w z) • y) := by
          module
      _ = 0 := by rw [e, sub_self]
  obtain ⟨-, h5⟩ := coords_eq_zero hd h3
  rcases mul_eq_zero.1 h5 with h | h
  · exact absurd h hne
  · exact h

theorem det2_eq_zero_of_eigen' (hd : det2 w y = 1) {M : Matrix (Fin 2) (Fin 2) F}
    (hMw : M *ᵥ w = t • w) (hMy : M *ᵥ y = t⁻¹ • y) (hne : t - t⁻¹ ≠ 0) {z : Fin 2 → F}
    (hz : M *ᵥ z = t⁻¹ • z) : det2 z y = 0 := by
  have h2 := diag_apply hd hMw hMy z
  have h1 := eq_basis hd z
  have h3 : ((t - t⁻¹) * det2 z y) • w + (0 : F) • y = 0 := by
    have e : (t * det2 z y) • w + (t⁻¹ * det2 w z) • y = t⁻¹ • z := by rw [← h2, hz]
    conv_rhs at e => rw [h1, smul_add, smul_smul, smul_smul]
    calc ((t - t⁻¹) * det2 z y) • w + (0 : F) • y
        = ((t * det2 z y) • w + (t⁻¹ * det2 w z) • y) -
          ((t⁻¹ * det2 z y) • w + (t⁻¹ * det2 w z) • y) := by
          module
      _ = 0 := by rw [e, sub_self]
  obtain ⟨h4, -⟩ := coords_eq_zero hd h3
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h hne
  · exact h

theorem commutes_diag (hd : det2 w y = 1) {M M' : Matrix (Fin 2) (Fin 2) F}
    (hMw : M *ᵥ w = t • w) (hMy : M *ᵥ y = t⁻¹ • y) (ht0 : t ≠ 0) (ht2 : t ^ 2 ≠ 1)
    (hc : ∀ u, M' *ᵥ (M *ᵥ u) = M *ᵥ (M' *ᵥ u)) :
    (∃ c : F, M' *ᵥ w = c • w) ∧ (∃ c' : F, M' *ᵥ y = c' • y) := by
  have hne : t⁻¹ - t ≠ 0 := by
    intro h
    apply ht2
    have h' : t⁻¹ = t := sub_eq_zero.1 h
    rw [pow_two]
    calc t * t = t * t⁻¹ := by rw [h']
      _ = 1 := mul_inv_cancel₀ ht0
  have hne' : t - t⁻¹ ≠ 0 := fun h => hne (by rw [← neg_sub, h, neg_zero])
  constructor
  · refine ⟨det2 (M' *ᵥ w) y, ?_⟩
    have hz : M *ᵥ (M' *ᵥ w) = t • (M' *ᵥ w) := by
      rw [← hc w, hMw, mulVec_smul]
    have h0 := det2_eq_zero_of_eigen hd hMw hMy hne hz
    calc M' *ᵥ w = det2 (M' *ᵥ w) y • w + det2 w (M' *ᵥ w) • y := eq_basis hd _
      _ = det2 (M' *ᵥ w) y • w := by rw [h0]; simp
  · refine ⟨det2 w (M' *ᵥ y), ?_⟩
    have hz : M *ᵥ (M' *ᵥ y) = t⁻¹ • (M' *ᵥ y) := by
      rw [← hc y, hMy, mulVec_smul]
    have h0 := det2_eq_zero_of_eigen' hd hMw hMy hne' hz
    calc M' *ᵥ y = det2 (M' *ᵥ y) y • w + det2 w (M' *ᵥ y) • y := eq_basis hd _
      _ = det2 w (M' *ᵥ y) • y := by rw [h0]; simp

end DiagFacts


section TwoElt

variable {F : Type} [Field F] [CharP F 2] {w y : Fin 2 → F}

theorem eq_one_of_eigen_two_pow (hd : det2 w y = 1) {M : SpecialLinearGroup (Fin 2) F}
    {c c' : F} (h1 : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ w = c • w)
    (h2 : (M : Matrix (Fin 2) (Fin 2) F) *ᵥ y = c' • y) {k : ℕ} (hk : M ^ (2 ^ k) = 1) :
    M = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw : w ≠ 0 := by
    intro h0
    rw [h0] at hd
    simp [det2] at hd
  have h3 : w = c ^ (2 ^ k) • w := by
    have := pow_mulVec_of_eigen h1 (2 ^ k)
    rwa [← Matrix.SpecialLinearGroup.coe_pow, hk, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec] at this
  have hcpow : c ^ (2 ^ k) = 1 := smul_left_injective F hw (by simpa using h3.symm)
  have hc : c = 1 := by
    have h4 : (c - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, hcpow, one_pow, sub_self]
    exact sub_eq_zero.1 ((pow_eq_zero_iff (pow_ne_zero k two_ne_zero)).1 h4)
  have hdet : c * c' = 1 := by
    have h5 := det2_mulVec (M : Matrix (Fin 2) (Fin 2) F) w y
    rw [h1, h2, det2_smul_left, det2_smul_right, hd, M.2] at h5
    simpa using h5
  have hc' : c' = 1 := by
    rw [hc, one_mul] at hdet
    exact hdet
  refine CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec (fun u => ?_)
  conv_lhs => rw [eq_basis hd u]
  conv_rhs => rw [eq_basis hd u]
  rw [mulVec_add, mulVec_smul, mulVec_smul, h1, h2, hc, hc']
  simp

end TwoElt

end CFSG.CGT.PushingUpLit.A78G0
