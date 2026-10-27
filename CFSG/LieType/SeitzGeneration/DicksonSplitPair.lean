module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.BenderSuzuki.MatrixGroups

variable {K : Type*} [Field K]

theorem eigenvector_cases {M P : Matrix (Fin 2) (Fin 2) K} {a b : K} (hP : P.det ≠ 0)
    (hab : a ≠ b) (hMP : M * P = P * diagonal ![a, b]) {x : Fin 2 → K} {c : K}
    (hx : M *ᵥ x = c • x) (hx0 : x ≠ 0) :
    (c = a ∧ ∃ t : K, x = t • fun i => P i 0) ∨ (c = b ∧ ∃ t : K, x = t • fun i => P i 1) := by
  have hU : IsUnit P.det := hP.isUnit
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hU
  have hiP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hU
  set y : Fin 2 → K := P⁻¹ *ᵥ x with hy
  have hxy : x = P *ᵥ y := by rw [hy, Matrix.mulVec_mulVec, hiP, Matrix.one_mulVec]
  have h1 : P *ᵥ (diagonal ![a, b] *ᵥ y) = P *ᵥ (c • y) := by
    calc P *ᵥ (diagonal ![a, b] *ᵥ y) = (P * diagonal ![a, b]) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]
      _ = (M * P) *ᵥ y := by rw [hMP]
      _ = M *ᵥ (P *ᵥ y) := by rw [← Matrix.mulVec_mulVec]
      _ = M *ᵥ x := by rw [← hxy]
      _ = c • x := hx
      _ = c • (P *ᵥ y) := by rw [← hxy]
      _ = P *ᵥ (c • y) := by rw [Matrix.mulVec_smul]
  have h2 : diagonal ![a, b] *ᵥ y = c • y := by
    have := congrArg (fun v => P⁻¹ *ᵥ v) h1
    simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hPi, Matrix.one_mul,
      Matrix.one_mulVec] using this
  have h20 : a * y 0 = c * y 0 := by
    have := congrFun h2 0
    simpa [Matrix.mulVec_diagonal] using this
  have h21 : b * y 1 = c * y 1 := by
    have := congrFun h2 1
    simpa [Matrix.mulVec_diagonal] using this
  have hxe : x = y 0 • (fun i => P i 0) + y 1 • fun i => P i 1 := by
    rw [hxy]
    ext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
  by_cases h0 : y 0 = 0
  · by_cases h1' : y 1 = 0
    · exact absurd (by rw [hxe, h0, h1']; simp) hx0
    · right
      refine ⟨mul_right_cancel₀ h1' h21.symm, y 1, ?_⟩
      rw [hxe, h0]
      simp
  · by_cases h1' : y 1 = 0
    · left
      refine ⟨mul_right_cancel₀ h0 h20.symm, y 0, ?_⟩
      rw [hxe, h1']
      simp
    · exfalso
      apply hab
      have ha := mul_right_cancel₀ h0 h20
      have hb := mul_right_cancel₀ h1' h21
      rw [ha, hb]

theorem mul_cancel_of_det_ne {X Y P : Matrix (Fin 2) (Fin 2) K} (hP : P.det ≠ 0)
    (h : X * P = Y * P) : X = Y := by
  have hiP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP.isUnit
  calc X = X * (P * P⁻¹) := by rw [hiP, Matrix.mul_one]
    _ = (X * P) * P⁻¹ := by rw [Matrix.mul_assoc]
    _ = (Y * P) * P⁻¹ := by rw [h]
    _ = Y := by rw [Matrix.mul_assoc, hiP, Matrix.mul_one]

theorem pow_mul_eq {A P : Matrix (Fin 2) (Fin 2) K} {μ : K}
    (hAP : A * P = P * diagonal ![μ, μ⁻¹]) (n : ℕ) :
    A ^ n * P = P * diagonal ![μ ^ n, μ⁻¹ ^ n] := by
  induction n with
  | zero =>
    have h1 : diagonal ![(1 : K), 1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    simp [h1]
  | succ n ih =>
    have hd : diagonal ![μ, μ⁻¹] * diagonal ![μ ^ n, μ⁻¹ ^ n] =
        diagonal ![μ ^ (n + 1), μ⁻¹ ^ (n + 1)] := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      ext i
      fin_cases i <;> simp [pow_succ, mul_comm]
    rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hAP, Matrix.mul_assoc, hd]

theorem ne_zero_of_diagonalizable {A : SpecialLinearGroup (Fin 2) K} {P : Matrix (Fin 2) (Fin 2) K}
    {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹]) : μ ≠ 0 := by
  intro h0
  have hd := congrArg Matrix.det hAP
  rw [Matrix.det_mul, Matrix.det_mul, A.2, one_mul, h0] at hd
  simp [Matrix.det_diagonal, Fin.prod_univ_two] at hd
  exact hP hd

theorem pow_mk_eq_one_iff {A : SpecialLinearGroup (Fin 2) K} {P : Matrix (Fin 2) (Fin 2) K}
    {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹]) (n : ℕ) :
    (A : PSL2MatrixGroup K) ^ n = 1 ↔ (μ ^ 2) ^ n = 1 := by
  have hμ := ne_zero_of_diagonalizable hP hAP
  have hpow : ((A ^ n : SpecialLinearGroup (Fin 2) K) : PSL2MatrixGroup K) =
      (A : PSL2MatrixGroup K) ^ n := (QuotientGroup.mk_pow _ _ _)
  rw [← hpow, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
  have hmat := pow_mul_eq hAP n
  have hAn : ((A ^ n : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K) ^ n := rfl
  rw [hAn]
  have hcol0 : P 0 0 ≠ 0 ∨ P 1 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP
    rw [Matrix.det_fin_two, hcon.1, hcon.2]
    ring
  have hcol1 : P 0 1 ≠ 0 ∨ P 1 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hP
    rw [Matrix.det_fin_two, hcon.1, hcon.2]
    ring
  constructor
  · rintro ⟨r, hr, hrA⟩
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have h1 : r • P = P * diagonal ![μ ^ n, μ⁻¹ ^ n] := by
      rw [← hmat, ← hrA]
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    have e0 : r = μ ^ n := by
      have h00 := congrFun (congrFun h1 0) 0
      have h10 := congrFun (congrFun h1 1) 0
      simp [Matrix.mul_apply, Matrix.diagonal_apply] at h00 h10
      rcases hcol0 with hi | hi
      · exact mul_right_cancel₀ hi (by rw [h00]; ring)
      · exact mul_right_cancel₀ hi (by rw [h10]; ring)
    have e1 : r = μ⁻¹ ^ n := by
      have h01 := congrFun (congrFun h1 0) 1
      have h11 := congrFun (congrFun h1 1) 1
      simp [Matrix.mul_apply, Matrix.diagonal_apply] at h01 h11
      rcases hcol1 with hi | hi
      · exact mul_right_cancel₀ hi (by rw [h01]; ring)
      · exact mul_right_cancel₀ hi (by rw [h11]; ring)
    have : (μ ^ 2) ^ n = r ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, ← e0]
    rw [this, hr2]
  · intro h
    refine ⟨μ ^ n, ?_, ?_⟩
    · have : (μ ^ n) ^ 2 = (μ ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      simpa [this] using h
    · have hr2 : (μ ^ n) ^ 2 = 1 := by
        have : (μ ^ n) ^ 2 = (μ ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
        rw [this, h]
      have hinv : μ⁻¹ ^ n = μ ^ n := by
        rw [inv_pow]
        have hne : μ ^ n ≠ 0 := pow_ne_zero n hμ
        field_simp
        linear_combination (-1 : K) * hr2
      symm
      refine mul_cancel_of_det_ne hP ?_
      rw [hmat, hinv]
      ext i j
      simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply]
      fin_cases j <;> simp [mul_comm]

theorem orderOf_mk_eq {A : SpecialLinearGroup (Fin 2) K} {P : Matrix (Fin 2) (Fin 2) K} {μ : K}
    (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹]) :
    orderOf (A : PSL2MatrixGroup K) = orderOf (μ ^ 2) := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_mk_eq_one_iff hP hAP]
    exact pow_orderOf_eq_one _
  · rw [orderOf_dvd_iff_pow_eq_one, ← pow_mk_eq_one_iff hP hAP]
    exact pow_orderOf_eq_one _

theorem mul_eq_smul_mul_of_commute {A B : SpecialLinearGroup (Fin 2) K}
    (h : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
      (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K)) :
    ∃ r : K, r ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) K) * B = r • ((B : Matrix (Fin 2) (Fin 2) K) * A) := by
  have h1 : ((A * B : SpecialLinearGroup (Fin 2) K) : PSL2MatrixGroup K) =
      ((B * A : SpecialLinearGroup (Fin 2) K) : PSL2MatrixGroup K) := h
  rw [QuotientGroup.eq, Matrix.SpecialLinearGroup.mem_center_iff] at h1
  obtain ⟨r, hr, hrA⟩ := h1
  have hr2 : r ^ 2 = 1 := by simpa using hr
  refine ⟨r, hr2, ?_⟩
  have hm : ((((A * B)⁻¹ * (B * A) : SpecialLinearGroup (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) =
      r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← hrA]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have h2 : (B * A : SpecialLinearGroup (Fin 2) K) = (A * B) * ((A * B)⁻¹ * (B * A)) := by group
  have h3 : ((B * A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      r • ((A : Matrix (Fin 2) (Fin 2) K) * B) := by
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, hm, Matrix.mul_smul, Matrix.mul_one]
    rfl
  have h3' : (B : Matrix (Fin 2) (Fin 2) K) * A = r • ((A : Matrix (Fin 2) (Fin 2) K) * B) := h3
  calc (A : Matrix (Fin 2) (Fin 2) K) * B = (r ^ 2) • ((A : Matrix (Fin 2) (Fin 2) K) * B) := by
        rw [hr2, one_smul]
    _ = r • (r • ((A : Matrix (Fin 2) (Fin 2) K) * B)) := by rw [smul_smul, sq]
    _ = r • ((B : Matrix (Fin 2) (Fin 2) K) * A) := by rw [h3']

theorem exists_common_eigenvector_of_commute {A B : SpecialLinearGroup (Fin 2) K}
    {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹]) (hμ4 : μ ^ 4 ≠ 1)
    (h : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
      (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K)) :
    ∃ x : Fin 2 → K, x ≠ 0 ∧ (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) ∧
      ∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x := by
  obtain ⟨r, hr2, hrAB⟩ := mul_eq_smul_mul_of_commute h
  have hμ0 := ne_zero_of_diagonalizable hP hAP
  have hμ2 : μ ^ 2 ≠ 1 := fun h2 => hμ4 (by rw [show μ ^ 4 = (μ ^ 2) ^ 2 by ring, h2]; norm_num)
  have hne : μ ≠ μ⁻¹ := by
    intro h2
    apply hμ2
    field_simp at h2
    linear_combination h2
  set x : Fin 2 → K := fun i => P i 0 with hx
  have hx0 : x ≠ 0 := by
    intro h0
    apply hP
    have h00 : P 0 0 = 0 := congrFun h0 0
    have h10 : P 1 0 = 0 := congrFun h0 1
    rw [Matrix.det_fin_two, h00, h10]
    ring
  have hAx : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = μ • x := by
    ext i
    have := congrFun (congrFun hAP i) 0
    simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct, hx]
      at this ⊢
    linear_combination this
  set y : Fin 2 → K := (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x with hy
  have hy0 : y ≠ 0 := by
    intro h0
    apply hx0
    have : (((B⁻¹ : SpecialLinearGroup (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ y = 0 := by
      rw [h0, Matrix.mulVec_zero]
    rw [hy, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this
    exact this
  have hAy : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ y = (r * μ) • y := by
    rw [hy, Matrix.mulVec_mulVec, hrAB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hAx,
      Matrix.mulVec_smul, smul_smul]
  rcases eigenvector_cases hP hne hAP hAy hy0 with ⟨hc, t, ht⟩ | ⟨hc, t, ht⟩
  · exact ⟨x, hx0, ⟨μ, hAx⟩, t, by rw [← hy, ht]⟩
  · exfalso
    apply hμ4
    have h1 : r * μ ^ 2 = 1 := by
      field_simp at hc
      linear_combination hc
    calc μ ^ 4 = r ^ 2 * μ ^ 4 := by rw [hr2, one_mul]
      _ = (r * μ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [h1]; norm_num

section Unipotent

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem sq_eq_zero_of_pow_eq_zero {T : Matrix (Fin 2) (Fin 2) K} {n : ℕ} (h : T ^ n = 0) :
    T * T = 0 := by
  have hCH : T * T = T.trace • T - T.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
  rcases n with _ | m
  · exfalso
    simp at h
  have hdet : T.det = 0 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 this
  rw [hdet, zero_smul, sub_zero] at hCH
  have hpow : ∀ k : ℕ, T ^ (k + 1) = T.trace ^ k • T := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, Matrix.smul_mul, hCH, smul_smul, ← pow_succ]
  rw [hpow m] at h
  rcases smul_eq_zero.1 h with h1 | h1
  · rw [hCH, pow_eq_zero_iff'.1 h1 |>.1, zero_smul] 
  · rw [hCH, h1, smul_zero]

theorem exists_nilpotent_of_pow_eq_one {N : SpecialLinearGroup (Fin 2) K}
    (hN1 : (N : PSL2MatrixGroup K) ≠ 1) (hNp : (N : PSL2MatrixGroup K) ^ p = 1) :
    ∃ r : K, r ^ 2 = 1 ∧ (N : Matrix (Fin 2) (Fin 2) K) - r • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 ∧
      ((N : Matrix (Fin 2) (Fin 2) K) - r • 1) * ((N : Matrix (Fin 2) (Fin 2) K) - r • 1) = 0 := by
  have hpow : ((N ^ p : SpecialLinearGroup (Fin 2) K) : PSL2MatrixGroup K) =
      (N : PSL2MatrixGroup K) ^ p := QuotientGroup.mk_pow _ _ _
  rw [← hpow, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at hNp
  obtain ⟨r, hr, hrN⟩ := hNp
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hsc : (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) K) =
      r • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hrp : r ^ p = r := by
    have h1 : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 h1 with h | h
    · have : r = 1 := sub_eq_zero.1 h
      rw [this, one_pow]
    · have : r = -1 := eq_neg_of_add_eq_zero_left h
      rw [this, neg_one_pow_char]
  refine ⟨r, hr2, ?_, ?_⟩
  · intro h0
    apply hN1
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨r, by simpa using hr, ?_⟩
    rw [hsc]
    exact (sub_eq_zero.1 h0).symm
  · apply sq_eq_zero_of_pow_eq_zero (n := p)
    have hc : Commute (N : Matrix (Fin 2) (Fin 2) K) (r • (1 : Matrix (Fin 2) (Fin 2) K)) :=
      (Commute.one_right _).smul_right r
    rw [sub_pow_char_of_commute p hc, smul_pow, one_pow, hrp]
    have hNp' : (N : Matrix (Fin 2) (Fin 2) K) ^ p = r • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hsc, hrN]
      rfl
    rw [hNp', sub_self]

end Unipotent

section Eigenline

theorem exists_smul_of_cross_eq {ℓ x : Fin 2 → K} (hℓ : ℓ ≠ 0) (h : ℓ 0 * x 1 = ℓ 1 * x 0) :
    ∃ t : K, x = t • ℓ := by
  by_cases h0 : ℓ 0 = 0
  · have h1 : ℓ 1 ≠ 0 := by
      intro h1
      apply hℓ
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨x 1 / ℓ 1, ?_⟩
    have hx0 : x 0 = 0 := by
      rw [h0, zero_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_left h1
    ext i
    fin_cases i <;> simp [h0, hx0, h1]
  · refine ⟨x 0 / ℓ 0, ?_⟩
    ext i
    fin_cases i
    · simp [h0]
    · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem exists_kernel_line {T : Matrix (Fin 2) (Fin 2) K} (hT : T ≠ 0) (hT2 : T * T = 0) :
    ∃ ℓ : Fin 2 → K, ℓ ≠ 0 ∧ T *ᵥ ℓ = 0 ∧
      ∀ x : Fin 2 → K, T *ᵥ x = 0 → ∃ t : K, x = t • ℓ := by
  have hcolker : ∀ j : Fin 2, T *ᵥ (fun i => T i j) = 0 := by
    intro j
    ext i
    have := congrFun (congrFun hT2 i) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  obtain ⟨ℓ, hℓ0, hℓ⟩ : ∃ ℓ : Fin 2 → K, ℓ ≠ 0 ∧ T *ᵥ ℓ = 0 := by
    by_cases h0 : (fun i => T i 0) = 0
    · refine ⟨fun i => T i 1, ?_, hcolker 1⟩
      intro h1
      apply hT
      ext i j
      fin_cases j
      · exact congrFun h0 i
      · exact congrFun h1 i
    · exact ⟨_, h0, hcolker 0⟩
  refine ⟨ℓ, hℓ0, hℓ, fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, T i 0 ≠ 0 ∨ T i 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hT
    ext i j
    fin_cases j
    · exact (hcon i).1
    · exact (hcon i).2
  have hxi : T i 0 * x 0 + T i 1 * x 1 = 0 := by
    have := congrFun hx i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hli : T i 0 * ℓ 0 + T i 1 * ℓ 1 = 0 := by
    have := congrFun hℓ i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  apply exists_smul_of_cross_eq hℓ0
  have e0 : T i 0 * (ℓ 0 * x 1 - ℓ 1 * x 0) = 0 := by linear_combination x 1 * hli - ℓ 1 * hxi
  have e1 : T i 1 * (ℓ 0 * x 1 - ℓ 1 * x 0) = 0 := by linear_combination ℓ 0 * hxi - x 0 * hli
  rcases hi with hi | hi
  · have := (mul_eq_zero.1 e0).resolve_left hi
    linear_combination this
  · have := (mul_eq_zero.1 e1).resolve_left hi
    linear_combination this

structure UniqueEigenline (M : Matrix (Fin 2) (Fin 2) K) (ℓ : Fin 2 → K) (r : K) : Prop where
  ne_zero : ℓ ≠ 0
  eigen : M *ᵥ ℓ = r • ℓ
  unique : ∀ (x : Fin 2 → K) (c : K), x ≠ 0 → M *ᵥ x = c • x → c = r ∧ ∃ t : K, x = t • ℓ

theorem uniqueEigenline_of_nilpotent {T : Matrix (Fin 2) (Fin 2) K} (hT : T ≠ 0)
    (hT2 : T * T = 0) (r : K) :
    ∃ ℓ, UniqueEigenline (T + r • (1 : Matrix (Fin 2) (Fin 2) K)) ℓ r := by
  obtain ⟨ℓ, hℓ0, hℓ, hker⟩ := exists_kernel_line hT hT2
  refine ⟨ℓ, hℓ0, ?_, ?_⟩
  · rw [Matrix.add_mulVec, hℓ, Matrix.smul_mulVec, Matrix.one_mulVec, zero_add]
  · intro x c hx0 hx
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hx
    have hTx : T *ᵥ x = (c - r) • x := by
      rw [sub_smul]
      rw [eq_sub_iff_add_eq]
      exact hx
    have h2 : (c - r) ^ 2 • x = 0 := by
      have : T *ᵥ (T *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, hT2, Matrix.zero_mulVec]
      rw [hTx, Matrix.mulVec_smul, hTx, smul_smul] at this
      simpa [sq] using this
    have hcr : c - r = 0 := by
      have : (c - r) ^ 2 = 0 := by
        rcases smul_eq_zero.1 h2 with h | h
        · exact h
        · exact absurd h hx0
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    refine ⟨sub_eq_zero.1 hcr, hker x ?_⟩
    rw [hTx, hcr, zero_smul]

theorem UniqueEigenline.conj {M X Xi : Matrix (Fin 2) (Fin 2) K} {ℓ : Fin 2 → K} {r : K}
    (h : UniqueEigenline M ℓ r) (hXi : Xi * X = 1) (hiX : X * Xi = 1) :
    UniqueEigenline (X * M * Xi) (X *ᵥ ℓ) r := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    apply h.ne_zero
    have : Xi *ᵥ (X *ᵥ ℓ) = 0 := by rw [h0, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec] at this
  · rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hXi, Matrix.mul_one, ← Matrix.mulVec_mulVec,
      h.eigen, Matrix.mulVec_smul]
  · intro x c hx0 hx
    have hx' : M *ᵥ (Xi *ᵥ x) = c • (Xi *ᵥ x) := by
      have h1 := congrArg (fun v => Xi *ᵥ v) hx
      have e : Xi * (X * M * Xi) = M * Xi := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at h1
      rw [e] at h1
      rwa [← Matrix.mulVec_mulVec] at h1
    have hxi0 : Xi *ᵥ x ≠ 0 := by
      intro h0
      apply hx0
      have : X *ᵥ (Xi *ᵥ x) = 0 := by rw [h0, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hiX, Matrix.one_mulVec] at this
    obtain ⟨hc, t, ht⟩ := h.unique _ c hxi0 hx'
    refine ⟨hc, t, ?_⟩
    have : X *ᵥ (Xi *ᵥ x) = X *ᵥ (t • ℓ) := by rw [ht]
    rwa [Matrix.mulVec_mulVec, hiX, Matrix.one_mulVec, Matrix.mulVec_smul] at this

theorem UniqueEigenline.exists_smul_of_comm {M M' : Matrix (Fin 2) (Fin 2) K} {ℓ : Fin 2 → K}
    {r s : K} (h : UniqueEigenline M ℓ r) (hs : s ≠ 0) (hcomm : M' * M = s • (M * M'))
    (hz : M' *ᵥ ℓ ≠ 0) : ∃ t : K, M' *ᵥ ℓ = t • ℓ := by
  have hz' : M *ᵥ (M' *ᵥ ℓ) = (s⁻¹ * r) • (M' *ᵥ ℓ) := by
    have h1 : M' *ᵥ (M *ᵥ ℓ) = s • (M *ᵥ (M' *ᵥ ℓ)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm, Matrix.smul_mulVec]
    rw [h.eigen, Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun v => s⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at h2
    exact h2.symm
  obtain ⟨-, t, ht⟩ := h.unique _ _ hz hz'
  exact ⟨t, ht⟩

end Eigenline

theorem SL_mulVec_ne_zero (X : SpecialLinearGroup (Fin 2) K) {v : Fin 2 → K} (hv : v ≠ 0) :
    (X : Matrix (Fin 2) (Fin 2) K) *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have : ((X⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ
      ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = 0 := by rw [h, Matrix.mulVec_zero]
  rwa [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at this

section Borel

variable {p : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_common_eigenvector_of_normal_pGroup {H : Subgroup (PSL2MatrixGroup K)}
    {E : Subgroup H} [E.Normal] [IsElementaryAbelian p E] (hE1 : E ≠ ⊥)
    {A B : SpecialLinearGroup (Fin 2) K} (hA : (A : PSL2MatrixGroup K) ∈ H)
    (hB : (B : PSL2MatrixGroup K) ∈ H) :
    ∃ x : Fin 2 → K, x ≠ 0 ∧ (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) ∧
      ∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x := by
  obtain ⟨e, he⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
  obtain ⟨N, hN⟩ := QuotientGroup.mk_surjective (((e : H) : PSL2MatrixGroup K))
  have hN1 : (N : PSL2MatrixGroup K) ≠ 1 := by
    intro h1
    apply he
    have : ((e : H) : PSL2MatrixGroup K) = 1 := by rw [← hN]; exact h1
    exact Subtype.ext (Subtype.ext this)
  have hNp : (N : PSL2MatrixGroup K) ^ p = 1 := by
    have h1 : (e : H) ^ p = 1 := by
      have := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (a := (e : H)) e.2
      exact this
    rw [show (N : PSL2MatrixGroup K) = ((e : H) : PSL2MatrixGroup K) from hN, ← Subgroup.coe_pow,
      h1, Subgroup.coe_one]
  obtain ⟨r, hr2, hT, hT2⟩ := exists_nilpotent_of_pow_eq_one hN1 hNp
  obtain ⟨ℓ, hU⟩ := uniqueEigenline_of_nilpotent hT hT2 r
  rw [sub_add_cancel] at hU
  have key : ∀ X : SpecialLinearGroup (Fin 2) K, (X : PSL2MatrixGroup K) ∈ H →
      ∃ t : K, (X : Matrix (Fin 2) (Fin 2) K) *ᵥ ℓ = t • ℓ := by
    intro X hX
    set h : H := ⟨(X : PSL2MatrixGroup K), hX⟩ with hh
    have he2 : h * (e : H) * h⁻¹ ∈ E := Subgroup.Normal.conj_mem inferInstance _ e.2 h
    have hcomm : (⟨h * (e : H) * h⁻¹, he2⟩ : E) * e = e * ⟨h * (e : H) * h⁻¹, he2⟩ :=
      IsMulCommutative.is_comm.comm _ _
    have hcomm' : (h * (e : H) * h⁻¹ : H) * (e : H) = (e : H) * (h * (e : H) * h⁻¹ : H) :=
      congrArg Subtype.val hcomm
    set N' : SpecialLinearGroup (Fin 2) K := X * N * X⁻¹ with hN'
    have hN'e : (N' : PSL2MatrixGroup K) = ((h * (e : H) * h⁻¹ : H) : PSL2MatrixGroup K) := by
      rw [hN']
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hN]
    have hcommP : (N' : PSL2MatrixGroup K) * (N : PSL2MatrixGroup K) =
        (N : PSL2MatrixGroup K) * (N' : PSL2MatrixGroup K) := by
      have h1 := congrArg Subtype.val hcomm'
      rw [hN'e, hN]
      simpa only [Subgroup.coe_mul] using h1
    obtain ⟨s, hs2, hs⟩ := mul_eq_smul_mul_of_commute hcommP
    have hs0 : s ≠ 0 := by
      rintro rfl
      norm_num at hs2
    have hz : (N' : Matrix (Fin 2) (Fin 2) K) *ᵥ ℓ ≠ 0 := SL_mulVec_ne_zero N' hU.ne_zero
    obtain ⟨t, ht⟩ := hU.exists_smul_of_comm hs0 hs hz
    have hXi : ((X⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (X : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hiX : (X : Matrix (Fin 2) (Fin 2) K) *
        ((X⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hU' := hU.conj hXi hiX
    have hN'mat : (N' : Matrix (Fin 2) (Fin 2) K) = (X : Matrix (Fin 2) (Fin 2) K) * N *
        ((X⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [hN']
      rfl
    rw [← hN'mat] at hU'
    obtain ⟨-, u, hu⟩ := hU'.unique ℓ t hU.ne_zero ht
    have hu0 : u ≠ 0 := by
      rintro rfl
      apply hU.ne_zero
      simpa using hu
    refine ⟨u⁻¹, ?_⟩
    calc (X : Matrix (Fin 2) (Fin 2) K) *ᵥ ℓ =
        u⁻¹ • (u • ((X : Matrix (Fin 2) (Fin 2) K) *ᵥ ℓ)) := by
          rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
      _ = u⁻¹ • ℓ := by rw [← hu]
  obtain ⟨t₁, ht₁⟩ := key A hA
  obtain ⟨t₂, ht₂⟩ := key B hB
  exact ⟨ℓ, hU.ne_zero, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩

end Borel

theorem card_SL_two (K : Type*) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K

theorem card_psl2_ge (F : Type*) [Field F] [Finite F] :
    Nat.card F * (Nat.card F ^ 2 - 1) ≤ 2 * Nat.card (PSL2MatrixGroup F) := by
  have h1 := card_SL_two F
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 2) F))
  have hz : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) ≤ 2 := by
    have := Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 2)).toEquiv
    rw [this]
    simpa using card_rootsOfUnity (k := 2) (R := F)
  rw [← h1, h2, mul_comm 2]
  exact Nat.mul_le_mul_left _ hz

theorem three_mul_pow_lt {p f m : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (h17 : 17 ≤ p ^ f)
    (hm0 : 0 < m) (hmf : m < f) (h3m : 3 * m ≤ 2 * f) : 3 * (p ^ m + 1) < p ^ f + 1 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hf5 : 5 ≤ f := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ f ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hm2 : m + 2 ≤ f := by omega
    have h1 : 2 ^ m * 4 ≤ 2 ^ f := by
      calc 2 ^ m * 4 = 2 ^ (m + 2) := by rw [pow_add]; norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · have hp5 : 5 ≤ p := by
      obtain ⟨k, hk⟩ := hodd
      have h2 := hp.two_le
      omega
    have hf2 : 2 ≤ f := by omega
    have hc : p ^ f = p ^ (f - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have h1 : p ^ m ≤ p ^ (f - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : 5 ≤ p ^ (f - 1) := by
      calc 5 ≤ p := hp5
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (f - 1) := Nat.pow_le_pow_right hp.pos (by omega)
    have h3 : p ^ (f - 1) * 5 ≤ p ^ f := by
      rw [hc]
      exact Nat.mul_le_mul_left _ hp5
    omega

open CFSG.Glauberman.Dickson CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
  CFSG.GorensteinWalter in
theorem card_ge_of_split_pair {p f : ℕ} [Fact p.Prime] [CharP K p]
    [Finite K] (hK : Nat.card K = p ^ (2 * f)) (hp3 : p ≠ 3) (h17 : 17 ≤ p ^ f) {M : ℕ}
    (hM6 : 6 ≤ M) (hM : p ^ f + 1 ≤ 3 * M) (H : Subgroup (PSL2MatrixGroup K))
    {A B : SpecialLinearGroup (Fin 2) K} (hA : (A : PSL2MatrixGroup K) ∈ H)
    (hB : (B : PSL2MatrixGroup K) ∈ H) {P : Matrix (Fin 2) (Fin 2) K} {μ : K} (hP : P.det ≠ 0)
    (hAP : (A : Matrix (Fin 2) (Fin 2) K) * P = P * diagonal ![μ, μ⁻¹])
    (hμM : M ≤ orderOf (μ ^ 2)) (hμq : (μ ^ 2) ^ (p ^ f + 1) = 1)
    (hB3 : 2 < orderOf (B : PSL2MatrixGroup K))
    (hno : ∀ x : Fin 2 → K, x ≠ 0 → (∃ c : K, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) →
      (∃ c : K, (B : Matrix (Fin 2) (Fin 2) K) *ᵥ x = c • x) → False) :
    p ^ f * ((p ^ f) ^ 2 - 1) ≤ 2 * Nat.card H := by
  classical
  have hp' : p.Prime := Fact.out
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have : f = 0 := by omega
    subst this
    simp at h17
  have hord1 : orderOf (A : PSL2MatrixGroup K) = orderOf (μ ^ 2) := orderOf_mk_eq hP hAP
  have hM1 : M ≤ orderOf (A : PSL2MatrixGroup K) := by rw [hord1]; exact hμM
  have hdvd1 : orderOf (A : PSL2MatrixGroup K) ∣ p ^ f + 1 := by
    rw [hord1]; exact orderOf_dvd_of_pow_eq_one hμq
  have hμ4 : μ ^ 4 ≠ 1 := by
    intro h4
    have h2 : orderOf (μ ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h4)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have hcop : Nat.Coprime p (p ^ f + 1) := by
    have : p ^ f + 1 = p * p ^ (f - 1) + 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hf1]
    rw [this, Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right p
  set a : H := ⟨(A : PSL2MatrixGroup K), hA⟩ with ha
  set b : H := ⟨(B : PSL2MatrixGroup K), hB⟩ with hb
  have hao : orderOf a = orderOf (A : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hbo : orderOf b = orderOf (B : PSL2MatrixGroup K) := Subgroup.orderOf_mk _ _
  have hcomm_false : (a * b = b * a) → False := by
    intro hab
    have hP' : (A : PSL2MatrixGroup K) * (B : PSL2MatrixGroup K) =
        (B : PSL2MatrixGroup K) * (A : PSL2MatrixGroup K) := congrArg Subtype.val hab
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_commute hP hAP hμ4 hP'
    exact hno x hx0 hxA hxB
  have ha6 : 6 ≤ orderOf a := by rw [hao]; exact le_trans hM6 hM1
  have hb3 : 2 < orderOf b := by rw [hbo]; exact hB3
  rcases dickson_psl2_subgroup_list hK H with
    ⟨m, hm, hmc, hel⟩ | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz2, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨-, ⟨e⟩⟩ | ⟨m, t, hm1, hmf, htm, htq, E, C, hEn, hEel, hEcard, hCcyc, hCcard, hdisj, hsup,
        hfaith, φ, hφ, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have := hel
    have h1 : (A : PSL2MatrixGroup K) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (p := p) (A := H) _ hA
    have h2 : orderOf (A : PSL2MatrixGroup K) ∣ p := orderOf_dvd_of_pow_eq_one h1
    have h3 := Nat.dvd_gcd h2 hdvd1
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  ·
    exfalso
    exact hcomm_false (hcyc.commGroup.mul_comm a b)
  ·
    exfalso
    exact hcomm_false (commute_of_equiv_dihedral e (x := a) (y := b) (by omega) hb3)
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_perm_four e a with h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    rcases orderOf_dvd_of_equiv_alternating_five e a with h | h | h <;>
      · have := Nat.le_of_dvd (by norm_num) h
        omega
  ·
    exfalso
    have := hEn
    have := hEel
    have hE1 : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hEcard
      have : p ^ m = p ^ 0 := by rw [← hEcard, pow_zero]
      have := Nat.pow_right_injective hp'.two_le this
      omega
    obtain ⟨x, hx0, hxA, hxB⟩ := exists_common_eigenvector_of_normal_pGroup hE1 hA hB
    exact hno x hx0 hxA hxB
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases hfm : f ≤ m
    · have h1 := card_psl2_ge (GaloisField p m)
      rw [hFm] at h1
      have h2 : Nat.card H = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_congr e.toEquiv
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ ≤ _ := h1
    · exfalso
      push Not at hfm
      have h1 := psl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have h3m : 3 * m ≤ 2 * f := by
        obtain ⟨c, hc⟩ := hmf
        rcases c with _ | _ | _ | c
        · omega
        · omega
        · omega
        · nlinarith
      have := three_mul_pow_lt hp' hp3 h17 (Nat.pos_of_ne_zero hm0) hfm h3m
      omega
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero, zero_dvd_iff] at hmf
      omega
    have hFm : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hmf' : m ∣ f := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hmf
    by_cases hfm : f ≤ m
    · have h2 : Nat.card H = p ^ m * (p ^ (2 * m) - 1) := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0]
      rw [h2]
      have hxy : p ^ f ≤ p ^ m := Nat.pow_le_pow_right hp'.pos hfm
      have : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
      calc p ^ f * ((p ^ f) ^ 2 - 1) ≤ p ^ m * ((p ^ m) ^ 2 - 1) :=
            Nat.mul_le_mul hxy (Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1)
        _ = p ^ m * (p ^ (2 * m) - 1) := by rw [this]
        _ ≤ 2 * (p ^ m * (p ^ (2 * m) - 1)) := Nat.le_mul_of_pos_left _ (by norm_num)
    · exfalso
      push Not at hfm
      have h1 := pgl2_orderOf_le (GaloisField p m) (e a)
      rw [MulEquiv.orderOf_eq, hFm, hao] at h1
      have h2m : 2 * m ≤ f :=
        MaxUp.two_mul_le_of_dvd_of_ne hmf' (Nat.ne_of_lt hfm) (by omega)
      have h3m : 3 * m ≤ 2 * f := by omega
      have := three_mul_pow_lt hp' hp3 h17 (Nat.pos_of_ne_zero hm0) hfm h3m
      omega

end CFSG.LieType.SeitzGeneration
