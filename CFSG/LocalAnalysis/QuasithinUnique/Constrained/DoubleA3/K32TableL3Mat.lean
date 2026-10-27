module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableReg
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.QuasithinUnique.DoubleA3

open Polynomial Matrix

section L3

variable {K : Type*} [Field K]

@[expose] def k32U3 (a b c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, a, b; 0, 1, c; 0, 0, 1]

theorem k32U3_zero : k32U3 (0 : K) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32U3]

theorem k32U3_sub_one_pow_three (a b c : K) : (k32U3 a b c - 1) ^ 3 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, k32U3, Matrix.one_apply]

theorem k32U3_cyclic {a b c : K} (ha : a ≠ 0) (hc : c ≠ 0) (w : Fin 3 → K) :
    ∃ p : K[X], w = (aeval (k32U3 a b c - 1) p).mulVec (Pi.single 2 1) := by
  set N : Matrix (Fin 3) (Fin 3) K := k32U3 a b c - 1 with hN
  have v1 : N.mulVec (Pi.single 2 1) = ![b, c, 0] := by
    ext i
    fin_cases i <;>
      simp [hN, k32U3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
  have v2 : N.mulVec ![b, c, 0] = ![a * c, 0, 0] := by
    ext i
    fin_cases i <;>
      simp [hN, k32U3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]
  have hac : a * c ≠ 0 := mul_ne_zero ha hc
  set x₀ := w 2 with hx₀
  set x₁ := w 1 / c with hx₁
  set x₂ := (w 0 - x₁ * b) / (a * c) with hx₂
  refine ⟨C x₀ + C x₁ * X + C x₂ * X ^ 2, ?_⟩
  have e0 : (aeval N) (C x₀ + C x₁ * X + C x₂ * X ^ 2) =
      x₀ • (1 : Matrix (Fin 3) (Fin 3) K) + x₁ • N + x₂ • N ^ 2 := by
    simp [Algebra.algebraMap_eq_smul_one]
  rw [e0]
  have hN2 : N ^ 2 = N * N := pow_two N
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hN2, ← Matrix.mulVec_mulVec,
    v1, v2]
  ext i
  fin_cases i
  · simp [Matrix.vecHead, Matrix.vecTail]
    rw [hx₂]
    field_simp
    ring
  · simp [Matrix.vecHead, Matrix.vecTail]
    rw [hx₁]
    field_simp
  · simp [Matrix.vecHead, Matrix.vecTail]
    exact hx₀.symm

theorem k32U3_commute_scalar [CharP K 2] {a b c : K} (ha : a ≠ 0) (hc : c ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) K} (hcomm : M * k32U3 a b c = k32U3 a b c * M) {c' : K}
    (hc' : c' ≠ 0) (hM : M ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K)) :
    ∃ x : K, M = x • (1 : Matrix (Fin 3) (Fin 3) K) := by
  set φ := Matrix.toLinAlgEquiv' (R := K) (n := Fin 3) with hφ
  have hu : Commute (k32U3 a b c) M := hcomm.symm
  have hNM : Commute (k32U3 a b c - 1) M := hu.sub_left (Commute.one_left M)
  have hNM' : Commute (φ (k32U3 a b c - 1)) (φ M) := hNM.map φ
  have hnil : IsNilpotent (φ (k32U3 a b c - 1)) :=
    IsNilpotent.map ⟨3, k32U3_sub_one_pow_three a b c⟩ φ
  have hcyc : ∀ w : Fin 3 → K, ∃ p : K[X],
      w = (aeval (φ (k32U3 a b c - 1)) p) (Pi.single 2 1 : Fin 3 → K) := by
    intro w
    obtain ⟨p, hp⟩ := k32U3_cyclic (b := b) ha hc w
    refine ⟨p, ?_⟩
    rw [aeval_algHom_apply]
    simpa [hφ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply] using hp
  have hA : φ M ^ 3 = algebraMap K (Module.End K (Fin 3 → K)) c' := by
    rw [← map_pow, hM, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
  obtain ⟨x, hx⟩ := k32_scalar_of_commute_cyclic hNM' hnil hcyc hc' hA
  refine ⟨x, φ.injective ?_⟩
  rw [hx, map_smul, map_one, Algebra.algebraMap_eq_smul_one]

theorem k32l3_comm_entries {T : Matrix (Fin 3) (Fin 3) K} {b c : K}
    (h : T * k32U3 0 b c = k32U3 0 b c * T) :
    b * T 2 0 = 0 ∧ b * T 2 1 = 0 ∧ c * T 2 0 = 0 ∧ c * T 2 1 = 0 ∧
    T 0 0 * b + T 0 1 * c = b * T 2 2 ∧ T 1 0 * b + T 1 1 * c = c * T 2 2 := by
  have e : ∀ i j : Fin 3, (T * k32U3 0 b c) i j = (k32U3 0 b c * T) i j := fun i j => by rw [h]
  have h00 := e 0 0
  have h01 := e 0 1
  have h10 := e 1 0
  have h11 := e 1 1
  have h02 := e 0 2
  have h12 := e 1 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, k32U3] at h00 h01 h10 h11
  simp [Matrix.mul_apply, Fin.sum_univ_three, k32U3] at h02 h12
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h00 with h | h <;> simp [h]
  · rcases h01 with h | h <;> simp [h]
  · rcases h10 with h | h <;> simp [h]
  · rcases h11 with h | h <;> simp [h]
  · linear_combination h02
  · linear_combination h12

theorem k32l3_form_scalar [CharP K 2] {T : Matrix (Fin 3) (Fin 3) K} {c' : K} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K))
    (h10 : T 1 0 = 0) (h01 : T 0 1 = 0) (h20 : T 2 0 = 0) (h21 : T 2 1 = 0)
    (h00 : T 0 0 = T 2 2) (h11 : T 1 1 = T 2 2) : ∃ x : K, T = x • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have c00 := congrFun (congrFun hT3 0) 0
  have c02 := congrFun (congrFun hT3 0) 2
  have c12 := congrFun (congrFun hT3 1) 2
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h10, h01, h20, h21, h00, h11] at c00 c02 c12
  set l := T 2 2 with hl
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at c00
    exact hc' (by simpa using c00.symm)
  have hx : T 0 2 = 0 := by
    have : l ^ 2 * T 0 2 = 0 := by linear_combination c02 - (l ^ 2 * T 0 2) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hl0)
  have hy : T 1 2 = 0 := by
    have : l ^ 2 * T 1 2 = 0 := by linear_combination c12 - (l ^ 2 * T 1 2) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hl0)
  refine ⟨l, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h20, h21, h00, h11, hx, hy]
  exact hl.symm

theorem k32l3_sigma_dep [CharP K 2] {T : Matrix (Fin 3) (Fin 3) K} {c' : K} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ¬ ∃ x : K, T = x • (1 : Matrix (Fin 3) (Fin 3) K))
    {b₁ c₁ b₂ c₂ : K} (h₁ : T * k32U3 0 b₁ c₁ = k32U3 0 b₁ c₁ * T)
    (h₂ : T * k32U3 0 b₂ c₂ = k32U3 0 b₂ c₂ * T) : b₁ * c₂ = b₂ * c₁ := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := k32l3_comm_entries h₁
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := k32l3_comm_entries h₂
  by_contra hne
  have hdet : b₁ * c₂ - b₂ * c₁ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have ht20 : T 2 0 = 0 := by
    by_contra h0
    apply hdet
    have hb₁ : b₁ = 0 := by
      have := a1
      exact (mul_eq_zero.mp this).resolve_right h0
    have hc₁ : c₁ = 0 := (mul_eq_zero.mp a3).resolve_right h0
    rw [hb₁, hc₁]
    ring
  have ht21 : T 2 1 = 0 := by
    by_contra h0
    apply hdet
    have hb₁ : b₁ = 0 := (mul_eq_zero.mp a2).resolve_right h0
    have hc₁ : c₁ = 0 := (mul_eq_zero.mp a4).resolve_right h0
    rw [hb₁, hc₁]
    ring
  have e00 : T 0 0 = T 2 2 := by
    refine mul_left_cancel₀ hdet ?_
    linear_combination c₂ * a5 - c₁ * d5
  have e01 : T 0 1 = 0 := by
    refine mul_left_cancel₀ hdet ?_
    linear_combination b₁ * d5 - b₂ * a5
  have e10 : T 1 0 = 0 := by
    refine mul_left_cancel₀ hdet ?_
    linear_combination c₂ * a6 - c₁ * d6
  have e11 : T 1 1 = T 2 2 := by
    refine mul_left_cancel₀ hdet ?_
    linear_combination b₁ * d6 - b₂ * a6
  exact hns (k32l3_form_scalar hc' hT3 e10 e01 ht20 ht21 e00 e11)

theorem k32l3_sigma_zero [CharP K 2] (hK : ∀ x : K, x ^ 4 = x) {T : Matrix (Fin 3) (Fin 3) K}
    (hdet : T.det = 1) {c' : K} (hc' : c' ≠ 0) (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ¬ ∃ x : K, T = x • (1 : Matrix (Fin 3) (Fin 3) K)) {b c : K}
    (h : T * k32U3 0 b c = k32U3 0 b c * T) : b = 0 ∧ c = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := k32l3_comm_entries h
  by_contra hbc
  have hbc' : b ≠ 0 ∨ c ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hbc hh
  have ht20 : T 2 0 = 0 := by
    rcases hbc' with hb | hc
    · exact (mul_eq_zero.mp a1).resolve_left hb
    · exact (mul_eq_zero.mp a3).resolve_left hc
  have ht21 : T 2 1 = 0 := by
    rcases hbc' with hb | hc
    · exact (mul_eq_zero.mp a2).resolve_left hb
    · exact (mul_eq_zero.mp a4).resolve_left hc
  have hdl : T 2 2 * (T 0 0 * T 1 1 - T 0 1 * T 1 0) = 1 := by
    rw [Matrix.det_fin_three] at hdet
    simp only [ht20, ht21] at hdet
    linear_combination hdet
  have hl0 : T 2 2 ≠ 0 := by
    intro h0
    rw [h0] at hdl
    simp at hdl
  have hl3 : T 2 2 ^ 3 = 1 := by
    have h4 := hK (T 2 2)
    have : T 2 2 * (T 2 2 ^ 3 - 1) = 0 := by linear_combination h4
    have := (mul_eq_zero.mp this).resolve_left hl0
    linear_combination this
  have c00 := congrFun (congrFun hT3 0) 0
  have c01 := congrFun (congrFun hT3 0) 1
  have c10 := congrFun (congrFun hT3 1) 0
  have c22 := congrFun (congrFun hT3 2) 2
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, ht20, ht21] at c00 c01 c10 c22
  have hc1 : c' = 1 := by
    have : c' = T 2 2 ^ 3 := by linear_combination -c22
    rw [this, hl3]
  rw [hc1] at c00
  have hδ : T 0 0 * T 1 1 - T 0 1 * T 1 0 = T 2 2 ^ 2 := by
    have : T 2 2 ^ 2 * (T 2 2 * (T 0 0 * T 1 1 - T 0 1 * T 1 0)) = T 2 2 ^ 2 * 1 := by rw [hdl]
    have h' : T 2 2 ^ 3 * (T 0 0 * T 1 1 - T 0 1 * T 1 0) = T 2 2 ^ 2 := by
      linear_combination this
    rw [hl3, one_mul] at h'
    exact h'
  have hD : (T 0 0 - T 2 2) * (T 1 1 - T 2 2) - T 0 1 * T 1 0 = 0 := by
    rcases hbc' with hb | hc
    · refine mul_left_cancel₀ hb ?_
      linear_combination (T 1 1 - T 2 2) * a5 - T 0 1 * a6
    · refine mul_left_cancel₀ hc ?_
      linear_combination (T 0 0 - T 2 2) * a6 - T 1 0 * a5
  have ht : T 0 0 + T 1 1 = 0 := by
    have : T 2 2 * (T 0 0 + T 1 1) = 0 := by
      linear_combination hδ - hD + (T 2 2) ^ 2 * h2
    exact (mul_eq_zero.mp this).resolve_left hl0
  have hy₂x₁ : T 1 1 = T 0 0 := by linear_combination ht - T 0 0 * h2
  rw [hy₂x₁] at c00 c01 c10 hδ
  have hx₂0 : T 0 1 = 0 := by
    have : T 2 2 ^ 2 * T 0 1 = 0 := by
      linear_combination c01 - T 0 1 * hδ - (T 0 0 ^ 2 * T 0 1 + T 0 1 ^ 2 * T 1 0) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hl0)
  rw [hx₂0] at c00 c10 hδ
  have hx₁sq : T 0 0 ^ 2 = T 2 2 ^ 2 := by linear_combination hδ
  have hx₁0 : T 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hx₁sq
    exact hl0 (pow_eq_zero_iff (two_ne_zero) |>.mp (by linear_combination -hx₁sq))
  have hy₁0 : T 1 0 = 0 := by
    have : T 0 0 ^ 2 * T 1 0 = 0 := by linear_combination c10 - (T 0 0 ^ 2 * T 1 0) * h2
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hx₁0)
  have hx₁l : T 0 0 = T 2 2 := by
    have h1 : T 0 0 ^ 3 = 1 := by linear_combination c00
    have : T 2 2 ^ 2 * (T 0 0 - T 2 2) = 0 := by
      linear_combination h1 - hl3 - T 0 0 * hx₁sq
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (pow_ne_zero 2 hl0))
  exact hns (k32l3_form_scalar hc' hT3 hy₁0 hx₂0 ht20 ht21 hx₁l (hy₂x₁.trans hx₁l))

theorem k32U3_mul (a b c a' b' c' : K) :
    k32U3 a b c * k32U3 a' b' c' = k32U3 (a + a') (b' + a * c' + b) (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32U3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem k32U3_eq_of_entries {A : Matrix (Fin 3) (Fin 3) K} (h10 : A 1 0 = 0) (h20 : A 2 0 = 0)
    (h21 : A 2 1 = 0) (h00 : A 0 0 = 1) (h11 : A 1 1 = 1) (h22 : A 2 2 = 1) :
    A = k32U3 (A 0 1) (A 0 2) (A 1 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32U3, h10, h20, h21, h00, h11, h22]

@[expose] def k32P0 (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem k32P0_mul_self : k32P0 K * k32P0 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32P0, Matrix.mul_apply, Fin.sum_univ_three]

theorem k32P0_transpose : (k32P0 K)ᵀ = k32P0 K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k32P0]

@[expose] def k32AntiT (X : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  k32P0 K * Xᵀ * k32P0 K

theorem k32AntiT_mul (X Y : Matrix (Fin 3) (Fin 3) K) :
    k32AntiT (X * Y) = k32AntiT Y * k32AntiT X := by
  unfold k32AntiT
  rw [Matrix.transpose_mul]
  calc k32P0 K * (Yᵀ * Xᵀ) * k32P0 K
      = k32P0 K * Yᵀ * (k32P0 K * k32P0 K) * Xᵀ * k32P0 K := by
        rw [k32P0_mul_self, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = k32P0 K * Yᵀ * k32P0 K * (k32P0 K * Xᵀ * k32P0 K) := by
        simp only [Matrix.mul_assoc]

theorem k32AntiT_one : k32AntiT (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  unfold k32AntiT
  rw [Matrix.transpose_one, Matrix.mul_one, k32P0_mul_self]

theorem k32AntiT_smul (x : K) (X : Matrix (Fin 3) (Fin 3) K) : k32AntiT (x • X) = x • k32AntiT X := by
  unfold k32AntiT
  rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem k32AntiT_involutive (X : Matrix (Fin 3) (Fin 3) K) : k32AntiT (k32AntiT X) = X := by
  unfold k32AntiT
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, k32P0_transpose]
  calc k32P0 K * (k32P0 K * (Xᵀᵀ * k32P0 K)) * k32P0 K
      = (k32P0 K * k32P0 K) * Xᵀᵀ * (k32P0 K * k32P0 K) := by simp only [Matrix.mul_assoc]
    _ = X := by rw [k32P0_mul_self, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]

theorem k32AntiT_U3 (a b : K) : k32AntiT (k32U3 a b 0) = k32U3 0 b a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp only [k32AntiT, Matrix.mul_apply, Fin.sum_univ_three]; simp [k32P0, k32U3])

theorem k32AntiT_pow_three (X : Matrix (Fin 3) (Fin 3) K) : k32AntiT (X ^ 3) = (k32AntiT X) ^ 3 := by
  rw [pow_succ, pow_two, k32AntiT_mul, k32AntiT_mul]
  simp only [pow_succ, pow_zero, one_mul]
  rw [Matrix.mul_assoc]

theorem k32AntiT_det (X : Matrix (Fin 3) (Fin 3) K) : (k32AntiT X).det = X.det := by
  unfold k32AntiT
  have h : (k32P0 K).det * (k32P0 K).det = 1 := by
    rw [← Matrix.det_mul, k32P0_mul_self, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  calc (k32P0 K).det * X.det * (k32P0 K).det = ((k32P0 K).det * (k32P0 K).det) * X.det := by ring
    _ = X.det := by rw [h, one_mul]

theorem k32l3_sigma_dep2 [CharP K 2] {T : Matrix (Fin 3) (Fin 3) K} {c' : K} (hc' : c' ≠ 0)
    (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ¬ ∃ x : K, T = x • (1 : Matrix (Fin 3) (Fin 3) K))
    {a₁ b₁ a₂ b₂ : K} (h₁ : T * k32U3 a₁ b₁ 0 = k32U3 a₁ b₁ 0 * T)
    (h₂ : T * k32U3 a₂ b₂ 0 = k32U3 a₂ b₂ 0 * T) : b₁ * a₂ = b₂ * a₁ := by
  have hcomm : ∀ {a b : K}, T * k32U3 a b 0 = k32U3 a b 0 * T →
      k32AntiT T * k32U3 0 b a = k32U3 0 b a * k32AntiT T := by
    intro a b h
    have := congrArg k32AntiT h
    rw [k32AntiT_mul, k32AntiT_mul, k32AntiT_U3] at this
    exact this.symm
  refine k32l3_sigma_dep (T := k32AntiT T) (c' := c') hc' ?_ ?_ (hcomm h₁) (hcomm h₂)
  · rw [← k32AntiT_pow_three, hT3, k32AntiT_smul, k32AntiT_one]
  · rintro ⟨x, hx⟩
    apply hns
    refine ⟨x, ?_⟩
    have := congrArg k32AntiT hx
    rwa [k32AntiT_involutive, k32AntiT_smul, k32AntiT_one] at this

theorem k32l3_sigma_zero2 [CharP K 2] (hK : ∀ x : K, x ^ 4 = x) {T : Matrix (Fin 3) (Fin 3) K}
    (hdet : T.det = 1) {c' : K} (hc' : c' ≠ 0) (hT3 : T ^ 3 = c' • (1 : Matrix (Fin 3) (Fin 3) K))
    (hns : ¬ ∃ x : K, T = x • (1 : Matrix (Fin 3) (Fin 3) K)) {a b : K}
    (h : T * k32U3 a b 0 = k32U3 a b 0 * T) : a = 0 ∧ b = 0 := by
  have hcomm : k32AntiT T * k32U3 0 b a = k32U3 0 b a * k32AntiT T := by
    have := congrArg k32AntiT h
    rw [k32AntiT_mul, k32AntiT_mul, k32AntiT_U3] at this
    exact this.symm
  have := k32l3_sigma_zero hK (T := k32AntiT T) (by rw [k32AntiT_det, hdet]) hc'
    (by rw [← k32AntiT_pow_three, hT3, k32AntiT_smul, k32AntiT_one])
    (by
      rintro ⟨x, hx⟩
      apply hns
      refine ⟨x, ?_⟩
      have := congrArg k32AntiT hx
      rwa [k32AntiT_involutive, k32AntiT_smul, k32AntiT_one] at this) hcomm
  exact ⟨this.2, this.1⟩


theorem k32_card_le_of_dep2 {T : Type*} [Finite T] {F : Type*} [Field F] [Finite F]
    (σ : T → F × F) (hσ : Function.Injective σ)
    (hdep : ∀ s t, (σ s).1 * (σ t).2 = (σ t).1 * (σ s).2) : Nat.card T ≤ Nat.card F := by
  by_cases hz : ∀ s, σ s = 0
  · have hsub : Subsingleton T := ⟨fun s t => hσ ((hz s).trans (hz t).symm)⟩
    have h1 : Nat.card T ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    exact h1.trans (Nat.succ_le_of_lt Nat.card_pos)
  · push Not at hz
    obtain ⟨s₀, hs₀⟩ := hz
    rcases hσs : σ s₀ with ⟨b₀, c₀⟩
    rw [hσs] at hs₀
    have hdep' : ∀ t, (σ t).1 * c₀ = b₀ * (σ t).2 := fun t => by
      have := hdep t s₀
      rwa [hσs] at this
    by_cases hb₀ : b₀ = 0
    · have hc₀ : c₀ ≠ 0 := fun hc₀ => hs₀ (by rw [hb₀, hc₀]; rfl)
      refine Nat.card_le_card_of_injective (fun t => (σ t).2) fun t t' htt => hσ ?_
      have h1 : (σ t).1 = 0 := by
        have := hdep' t
        rw [hb₀, zero_mul] at this
        exact (mul_eq_zero.mp this).resolve_right hc₀
      have h2 : (σ t').1 = 0 := by
        have := hdep' t'
        rw [hb₀, zero_mul] at this
        exact (mul_eq_zero.mp this).resolve_right hc₀
      exact Prod.ext (h1.trans h2.symm) htt
    · refine Nat.card_le_card_of_injective (fun t => (σ t).1) fun t t' htt => hσ ?_
      refine Prod.ext htt (mul_left_cancel₀ hb₀ ?_)
      rw [← hdep' t, ← hdep' t']
      simp only at htt
      rw [htt]


end L3

end CFSG.QuasithinUnique.DoubleA3
