module

public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU antidiag_mul_single single_mul_antidiag)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)

variable {K : Type} [Field K]

@[expose] def uMat (n : ℕ) (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d, a ^ 2 ^ n * c + b ^ 2 ^ n, a ^ 2 ^ n, 1]

@[expose] def UCond (n : ℕ) (a b c d : K) : Prop :=
  c ^ 2 ^ n = c ∧ d + d ^ 2 ^ n = a ^ 2 ^ n * b + a * b ^ 2 ^ n

@[expose] def wMat (n : ℕ) (a b c d : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, a ^ 2 ^ n, a ^ 2 ^ n * c + b ^ 2 ^ n, d; 0, 1, c, b; 0, 0, 1, a; 0, 0, 0, 1]

@[expose] def IsLowerUni (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (∀ i j, i < j → A i j = 0) ∧ ∀ i, A i i = 1

@[expose] def IsUpperUni (A : Matrix (Fin 4) (Fin 4) K) : Prop :=
  (∀ i j, j < i → A i j = 0) ∧ ∀ i, A i i = 1

private theorem rev0 : Fin.rev (0 : Fin 4) = 3 := rfl
private theorem rev1 : Fin.rev (1 : Fin 4) = 2 := rfl
private theorem rev2 : Fin.rev (2 : Fin 4) = 1 := rfl
private theorem rev3 : Fin.rev (3 : Fin 4) = 0 := rfl

theorem det_uMat (n : ℕ) (a b c d : K) : (uMat n a b c d).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [uMat, Fin.prod_univ_four]
  · intro i j h
    have hij : i < j := OrderDual.toDual_lt_toDual.mp h
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [uMat]

theorem det_wMat (n : ℕ) (a b c d : K) : (wMat n a b c d).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [wMat, Fin.prod_univ_four]
  · intro i j h
    have hji : j < i := h
    fin_cases i <;> fin_cases j <;> first | exact absurd hji (by decide) | simp [wMat]

@[expose] def uSL (n : ℕ) (a b c d : K) : SL(4, K) := ⟨uMat n a b c d, det_uMat n a b c d⟩

@[expose] def wSL (n : ℕ) (a b c d : K) : SL(4, K) := ⟨wMat n a b c d, det_wMat n a b c d⟩

theorem toGL_uSL (n : ℕ) (a b c d : K) :
    ((Matrix.SpecialLinearGroup.toGL (uSL n a b c d) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = uMat n a b c d :=
  rfl

theorem J_mul_J : (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * antidiag 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, rev0, rev1, rev2, rev3]

theorem J_mul_J_assoc (X : Matrix (Fin 4) (Fin 4) K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (antidiag 4 * X) = X := by
  rw [← Matrix.mul_assoc, J_mul_J, Matrix.one_mul]

theorem J_mul_mul_J_apply (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (((antidiag 4 : Matrix (Fin 4) (Fin 4) K) * M * antidiag 4 : Matrix (Fin 4) (Fin 4) K)) i j =
      M (Fin.rev i) (Fin.rev j) := by
  fin_cases i <;> fin_cases j <;>
    simp [antidiag, Matrix.mul_apply, Fin.sum_univ_four, rev0, rev1, rev2, rev3]

theorem J_mul_single_mul_J (i j : Fin 4) (x : K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * single i j x * antidiag 4 =
      single (Fin.rev i) (Fin.rev j) x := by
  rw [antidiag_mul_single, single_mul_antidiag]

theorem J_conj_one_add_single (i j : Fin 4) (x : K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (1 + single i j x) * antidiag 4 =
      1 + single (Fin.rev i) (Fin.rev j) x := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, J_mul_J, J_mul_single_mul_J]

theorem J_conj_mul (A B : Matrix (Fin 4) (Fin 4) K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (A * B) * antidiag 4 =
      (antidiag 4 * A * antidiag 4) * (antidiag 4 * B * antidiag 4) := by
  simp only [Matrix.mul_assoc, J_mul_J_assoc]

theorem J_mul_mul_J_mul_J_mul (M : Matrix (Fin 4) (Fin 4) K) :
    (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * (antidiag 4 * M * antidiag 4) * antidiag 4 = M := by
  simp only [Matrix.mul_assoc, J_mul_J_assoc, J_mul_J, Matrix.mul_one]

theorem wMat_eq_J_mul_uMat_mul_J (n : ℕ) (a b c d : K) :
    wMat n a b c d = antidiag 4 * uMat n a b c d * antidiag 4 := by
  ext i j
  rw [J_mul_mul_J_apply]
  fin_cases i <;> fin_cases j <;> simp [wMat, uMat, rev0, rev1, rev2, rev3]

@[expose] def jGL (K : Type) [Field K] : GL (Fin 4) K :=
  Units.mk (antidiag 4) (antidiag 4) J_mul_J J_mul_J

theorem jGL_inv (K : Type) [Field K] : (jGL K)⁻¹ = jGL K :=
  inv_eq_of_mul_eq_one_right (Units.ext J_mul_J)

theorem jGL_conj_val (K : Type) [Field K] (M : GL (Fin 4) K) :
    ((jGL K * M * jGL K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      antidiag 4 * (M : Matrix (Fin 4) (Fin 4) K) * antidiag 4 :=
  rfl

theorem isLowerUni_one : IsLowerUni (1 : Matrix (Fin 4) (Fin 4) K) :=
  ⟨fun _ _ hij => Matrix.one_apply_ne (ne_of_lt hij), fun i => Matrix.one_apply_eq i⟩

theorem isUpperUni_one : IsUpperUni (1 : Matrix (Fin 4) (Fin 4) K) :=
  ⟨fun _ _ hji => Matrix.one_apply_ne (ne_of_gt hji), fun i => Matrix.one_apply_eq i⟩

theorem isLowerUni_mul {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsLowerUni A)
    (hB : IsLowerUni B) : IsLowerUni (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i < k
    · rw [hA.1 i k hik, zero_mul]
    · rw [hB.1 k j (lt_of_le_of_lt (not_lt.mp hik) hij), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, one_mul, hB.2 i]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hB.1 k i h, mul_zero]
      · rw [hA.1 i k h, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUpperUni_mul {A B : Matrix (Fin 4) (Fin 4) K} (hA : IsUpperUni A)
    (hB : IsUpperUni B) : IsUpperUni (A * B) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k < i
    · rw [hA.1 i k hki, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le hji (not_lt.mp hki)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, one_mul, hB.2 i]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem isUpperUni_J_mul_mul_J {M : Matrix (Fin 4) (Fin 4) K} (h : IsLowerUni M) :
    IsUpperUni ((antidiag 4 : Matrix (Fin 4) (Fin 4) K) * M * antidiag 4) := by
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [J_mul_mul_J_apply]
    exact h.1 _ _ (Fin.rev_lt_rev.mpr hji)
  · rw [J_mul_mul_J_apply]
    exact h.2 _

theorem isLowerUni_J_mul_mul_J {M : Matrix (Fin 4) (Fin 4) K} (h : IsUpperUni M) :
    IsLowerUni ((antidiag 4 : Matrix (Fin 4) (Fin 4) K) * M * antidiag 4) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [J_mul_mul_J_apply]
    exact h.1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [J_mul_mul_J_apply]
    exact h.2 _

theorem strictLower_pow_four (N : Matrix (Fin 4) (Fin 4) K) (hN : ∀ i j, i ≤ j → N i j = 0) :
    N ^ 4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, hN]

theorem strictUpper_pow_four (N : Matrix (Fin 4) (Fin 4) K) (hN : ∀ i j, j ≤ i → N i j = 0) :
    N ^ 4 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, hN]

section CharTwo

variable [CharP K 2]

theorem one_add_sq_of_charTwo (x : Matrix (Fin 4) (Fin 4) K) : (1 + x) ^ 2 = 1 + x ^ 2 := by
  have hxx : x + x = 0 := by
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero (x i j)
  calc (1 + x) ^ 2 = 1 + x ^ 2 + (x + x) := by noncomm_ring
    _ = 1 + x ^ 2 := by rw [hxx, add_zero]

theorem pow_four_of_unipotent (N : Matrix (Fin 4) (Fin 4) K) (hN : N ^ 4 = 0) :
    (1 + N) ^ 4 = 1 := by
  have h4 : (N ^ 2) ^ 2 = N ^ 4 := (pow_mul N 2 2).symm
  have h4' : ((1 + N) ^ 2) ^ 2 = (1 + N) ^ 4 := (pow_mul (1 + N) 2 2).symm
  rw [← h4', one_add_sq_of_charTwo, one_add_sq_of_charTwo, h4, hN, add_zero]

theorem isLowerUni_pow_four {A : Matrix (Fin 4) (Fin 4) K} (hA : IsLowerUni A) : A ^ 4 = 1 := by
  have hN : ∀ i j : Fin 4, i ≤ j → (A - 1) i j = 0 := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · rw [Matrix.sub_apply, hA.1 i j h, Matrix.one_apply_ne (ne_of_lt h), sub_zero]
    · subst h
      rw [Matrix.sub_apply, hA.2 i, Matrix.one_apply_eq, sub_self]
  have h := pow_four_of_unipotent (A - 1) (strictLower_pow_four (A - 1) hN)
  have e : (1 : Matrix (Fin 4) (Fin 4) K) + (A - 1) = A := by abel
  rwa [e] at h

theorem isUpperUni_pow_four {A : Matrix (Fin 4) (Fin 4) K} (hA : IsUpperUni A) : A ^ 4 = 1 := by
  have hN : ∀ i j : Fin 4, j ≤ i → (A - 1) i j = 0 := by
    intro i j hji
    rcases hji.lt_or_eq with h | h
    · rw [Matrix.sub_apply, hA.1 i j h, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · rw [h, Matrix.sub_apply, hA.2 i, Matrix.one_apply_eq, sub_self]
  have h := pow_four_of_unipotent (A - 1) (strictUpper_pow_four (A - 1) hN)
  have e : (1 : Matrix (Fin 4) (Fin 4) K) + (A - 1) = A := by abel
  rwa [e] at h

theorem isLowerUni_coe_inv {g : GL (Fin 4) K}
    (hg : IsLowerUni (g : Matrix (Fin 4) (Fin 4) K)) :
    IsLowerUni ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have h4 : (g : Matrix (Fin 4) (Fin 4) K) ^ 4 = 1 := isLowerUni_pow_four hg
  have hinv : ((g : Matrix (Fin 4) (Fin 4) K))⁻¹ =
      (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) *
        (g : Matrix (Fin 4) (Fin 4) K) := by
    refine Matrix.inv_eq_right_inv ?_
    calc (g : Matrix (Fin 4) (Fin 4) K) * ((g : Matrix (Fin 4) (Fin 4) K) *
          (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K))
        = (g : Matrix (Fin 4) (Fin 4) K) ^ 4 := by noncomm_ring
      _ = 1 := h4
  rw [Matrix.coe_units_inv, hinv]
  exact isLowerUni_mul (isLowerUni_mul hg hg) hg

theorem isUpperUni_coe_inv {g : GL (Fin 4) K}
    (hg : IsUpperUni (g : Matrix (Fin 4) (Fin 4) K)) :
    IsUpperUni ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have h4 : (g : Matrix (Fin 4) (Fin 4) K) ^ 4 = 1 := isUpperUni_pow_four hg
  have hinv : ((g : Matrix (Fin 4) (Fin 4) K))⁻¹ =
      (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K) *
        (g : Matrix (Fin 4) (Fin 4) K) := by
    refine Matrix.inv_eq_right_inv ?_
    calc (g : Matrix (Fin 4) (Fin 4) K) * ((g : Matrix (Fin 4) (Fin 4) K) *
          (g : Matrix (Fin 4) (Fin 4) K) * (g : Matrix (Fin 4) (Fin 4) K))
        = (g : Matrix (Fin 4) (Fin 4) K) ^ 4 := by noncomm_ring
      _ = 1 := h4
  rw [Matrix.coe_units_inv, hinv]
  exact isUpperUni_mul (isUpperUni_mul hg hg) hg

@[expose] def lowerUniGL (K : Type) [Field K] [CharP K 2] : Subgroup (GL (Fin 4) K) where
  carrier := {g | IsLowerUni (g : Matrix (Fin 4) (Fin 4) K)}
  mul_mem' hg hh := isLowerUni_mul hg hh
  one_mem' := isLowerUni_one
  inv_mem' hg := isLowerUni_coe_inv hg

@[expose] def upperUniGL (K : Type) [Field K] [CharP K 2] : Subgroup (GL (Fin 4) K) where
  carrier := {g | IsUpperUni (g : Matrix (Fin 4) (Fin 4) K)}
  mul_mem' hg hh := isUpperUni_mul hg hh
  one_mem' := isUpperUni_one
  inv_mem' hg := isUpperUni_coe_inv hg

end CharTwo

section CharTwoJ

variable [CharP K 2]

theorem det_antidiag : (antidiag 4 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd2 : (antidiag 4 : Matrix (Fin 4) (Fin 4) K).det *
      (antidiag 4 : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [← Matrix.det_mul, J_mul_J, Matrix.det_one]
  have h0 : ((antidiag 4 : Matrix (Fin 4) (Fin 4) K).det + 1) *
      ((antidiag 4 : Matrix (Fin 4) (Fin 4) K).det + 1) = 0 := by
    linear_combination hd2 + ((antidiag 4 : Matrix (Fin 4) (Fin 4) K).det + 1) * hchar
  have h1 := mul_self_eq_zero.mp h0
  linear_combination h1 - hchar

theorem mem_SU_J (σ : K ≃+* K) : jGL K ∈ SU σ 4 := by
  refine mem_SU.mpr ⟨det_antidiag, ?_⟩
  have hc : conjTr σ (antidiag 4 : Matrix (Fin 4) (Fin 4) K) = antidiag 4 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, antidiag, rev0, rev1, rev2, rev3]
  show conjTr σ (antidiag 4 : Matrix (Fin 4) (Fin 4) K) * antidiag 4 * antidiag 4 = antidiag 4
  rw [hc, J_mul_J, Matrix.one_mul]

@[expose] def jSU (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    SU (unitaryInvolution K 2 n) 4 :=
  ⟨jGL K, mem_SU_J _⟩

end CharTwoJ

section Unitary

variable [Finite K] [CharP K 2]

theorem pow_pow_of_card {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (x : K) :
    (x ^ 2 ^ n) ^ 2 ^ n = x := by
  have h := unitaryInvolution_involutive hK x
  rwa [unitaryInvolution_apply, unitaryInvolution_apply] at h

theorem uMat_conj_mul (n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) :
    conjTr (unitaryInvolution K 2 n) (uMat n a b c d) * antidiag 4 * uMat n a b c d =
      (antidiag 4 : Matrix (Fin 4) (Fin 4) K) := by
  obtain ⟨h1, h2⟩ := h
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, antidiag, uMat, unitaryInvolution_apply, iterateFrobenius_def,
      Matrix.mul_apply, Fin.sum_univ_four, pow_pow_of_card hK, h1, mul_pow, add_pow_char_pow, rev0, rev1, rev2, rev3] <;>
    first
    | ring1
    | linear_combination h2 + (a ^ 2 ^ n * b + a * b ^ 2 ^ n) * hchar
    | linear_combination (a ^ 2 ^ n * c + b ^ 2 ^ n) * hchar
    | linear_combination (a ^ 2 ^ n) * hchar
    | linear_combination (b + a * c) * hchar
    | linear_combination c * hchar
    | linear_combination a * hchar

theorem uMat_mem_SU (n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) :
    Matrix.SpecialLinearGroup.toGL (uSL n a b c d) ∈ SU (unitaryInvolution K 2 n) 4 := by
  refine mem_SU.mpr ⟨det_uMat n a b c d, ?_⟩
  rw [toGL_uSL]
  exact uMat_conj_mul n hK h

theorem uCond_of_lower (n : ℕ) {G : Matrix (Fin 4) (Fin 4) K}
    (hz : ∀ i j, i < j → G i j = 0) (hd : ∀ i, G i i = 1)
    (hE : conjTr (unitaryInvolution K 2 n) G * antidiag 4 * G =
      (antidiag 4 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ a b c d : K, UCond n a b c d ∧ G = uMat n a b c d := by
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  have E00 := congrFun (congrFun hE 0) 0
  have E01 := congrFun (congrFun hE 0) 1
  have E02 := congrFun (congrFun hE 0) 2
  have E11 := congrFun (congrFun hE 1) 1
  simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_four, unitaryInvolution_apply,
    iterateFrobenius_def, hz, hd, rev0, rev1, rev2, rev3] at E00 E01 E02 E11
  have h2 : G 3 0 + G 3 0 ^ 2 ^ n = G 1 0 ^ 2 ^ n * G 2 0 + G 1 0 * G 2 0 ^ 2 ^ n := by
    linear_combination E00 - (G 1 0 ^ 2 ^ n * G 2 0 + G 1 0 * G 2 0 ^ 2 ^ n) * hchar
  have h31 : G 3 1 = G 1 0 ^ 2 ^ n * G 2 1 + G 2 0 ^ 2 ^ n := by
    linear_combination E01 - (G 1 0 ^ 2 ^ n * G 2 1 + G 2 0 ^ 2 ^ n) * hchar
  have h32 : G 3 2 = G 1 0 ^ 2 ^ n := by
    linear_combination E02 - (G 1 0 ^ 2 ^ n) * hchar
  have hc : G 2 1 ^ 2 ^ n = G 2 1 := by
    linear_combination E11 - (G 2 1) * hchar
  refine ⟨G 1 0, G 2 0, G 2 1, G 3 0, ⟨hc, h2⟩, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat, hz, hd, h31, h32]

theorem exists_uCond_of_mem (n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2) {g : GL (Fin 4) K}
    (hg : g ∈ SU (unitaryInvolution K 2 n) 4) (hl : IsLowerUni (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ a b c d : K, UCond n a b c d ∧ (g : Matrix (Fin 4) (Fin 4) K) = uMat n a b c d :=
  uCond_of_lower n hl.1 hl.2 (mem_SU.mp hg).2

end Unitary

section Factor

variable [CharP K 2]

theorem uMat_eq_prod (n : ℕ) {a b c d : K} (h : UCond n a b c d) :
    uMat n a b c d = (1 + single 3 2 (a ^ 2 ^ n)) * ((1 + single 3 1 (b ^ 2 ^ n)) *
      ((1 + single 3 0 (d ^ 2 ^ n)) * ((1 + single 2 1 c) *
        ((1 + single 2 0 (b + a * c)) * (1 + single 1 0 a))))) := by
  obtain ⟨h1, h2⟩ := h
  have hchar : (2 : K) = 0 := CharTwo.two_eq_zero
  have t1 : (1 + single 2 0 (b + a * c) : Matrix (Fin 4) (Fin 4) K) * (1 + single 1 0 a) =
      !![1, 0, 0, 0; a, 1, 0, 0; b + a * c, 0, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply]
  have t2 : (1 + single 2 1 c : Matrix (Fin 4) (Fin 4) K) *
      !![1, 0, 0, 0; a, 1, 0, 0; b + a * c, 0, 1, 0; 0, 0, 0, 1] =
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; 0, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply] <;>
      first
      | ring1
      | linear_combination (a * c) * hchar
  have t3 : (1 + single 3 0 (d ^ 2 ^ n) : Matrix (Fin 4) (Fin 4) K) *
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; 0, 0, 0, 1] =
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d ^ 2 ^ n, 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply]
  have t4 : (1 + single 3 1 (b ^ 2 ^ n) : Matrix (Fin 4) (Fin 4) K) *
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d ^ 2 ^ n, 0, 0, 1] =
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d ^ 2 ^ n + b ^ 2 ^ n * a, b ^ 2 ^ n, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply] <;> ring1
  have t5 :(1 + single 3 2 (a ^ 2 ^ n) : Matrix (Fin 4) (Fin 4) K) *
      !![1, 0, 0, 0; a, 1, 0, 0; b, c, 1, 0; d ^ 2 ^ n + b ^ 2 ^ n * a, b ^ 2 ^ n, 0, 1] =
      uMat n a b c d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply, Matrix.single_apply] <;>
      first
      | ring1
      | linear_combination h2 + (a * b ^ 2 ^ n + a ^ 2 ^ n * b - d) * hchar
  rw [t1, t2, t3, t4, t5]

theorem uSL_eq_prod (n : ℕ) {a b c d : K} (h : UCond n a b c d) :
    uSL n a b c d =
      Matrix.SpecialLinearGroup.transvection (i := (3 : Fin 4)) (j := (2 : Fin 4)) (by decide)
        (a ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (3 : Fin 4)) (j := (1 : Fin 4)) (by decide)
        (b ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (3 : Fin 4)) (j := (0 : Fin 4)) (by decide)
        (d ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := (1 : Fin 4)) (by decide) c *
      Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide)
        (b + a * c) *
      Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := (0 : Fin 4)) (by decide) a := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_assoc]
  exact uMat_eq_prod n h

theorem wSL_eq_prod (n : ℕ) {a b c d : K} (h : UCond n a b c d) :
    wSL n a b c d =
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := (1 : Fin 4)) (by decide)
        (a ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := (2 : Fin 4)) (by decide)
        (b ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
        (d ^ 2 ^ n) *
      Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by decide) c *
      Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
        (b + a * c) *
      Matrix.SpecialLinearGroup.transvection (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide) a := by
  apply Subtype.ext
  show wMat n a b c d = _
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_assoc]
  rw [wMat_eq_J_mul_uMat_mul_J, uMat_eq_prod n h]
  simp only [J_conj_mul, J_conj_one_add_single, rev0, rev1, rev2, rev3]

end Factor

section UnitaryUpper

variable [Finite K] [CharP K 2]

theorem wMat_mem_SU (n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2) {a b c d : K}
    (h : UCond n a b c d) :
    Matrix.SpecialLinearGroup.toGL (wSL n a b c d) ∈ SU (unitaryInvolution K 2 n) 4 := by
  have e : Matrix.SpecialLinearGroup.toGL (wSL n a b c d) =
      jGL K * Matrix.SpecialLinearGroup.toGL (uSL n a b c d) * (jGL K)⁻¹ := by
    rw [jGL_inv]
    apply Units.ext
    exact wMat_eq_J_mul_uMat_mul_J n a b c d
  rw [e]
  exact mul_mem (mul_mem (mem_SU_J _) (uMat_mem_SU n hK h)) (inv_mem (mem_SU_J _))

theorem exists_wCond_of_mem (n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2) {g : GL (Fin 4) K}
    (hg : g ∈ SU (unitaryInvolution K 2 n) 4) (hu : IsUpperUni (g : Matrix (Fin 4) (Fin 4) K)) :
    ∃ a b c d : K, UCond n a b c d ∧ (g : Matrix (Fin 4) (Fin 4) K) = wMat n a b c d := by
  have hg' : jGL K * g * (jGL K)⁻¹ ∈ SU (unitaryInvolution K 2 n) 4 :=
    mul_mem (mul_mem (mem_SU_J _) hg) (inv_mem (mem_SU_J _))
  have hl : IsLowerUni ((jGL K * g * (jGL K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [jGL_inv, jGL_conj_val]
    exact isLowerUni_J_mul_mul_J hu
  obtain ⟨a, b, c, d, hc, he⟩ := exists_uCond_of_mem n hK hg' hl
  refine ⟨a, b, c, d, hc, ?_⟩
  rw [jGL_inv, jGL_conj_val] at he
  rw [wMat_eq_J_mul_uMat_mul_J, ← he, J_mul_mul_J_mul_J_mul]

end UnitaryUpper

section Subgroups

variable [Finite K] [CharP K 2]

@[expose] noncomputable def LowerU (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Subgroup (SU (unitaryInvolution K 2 n) 4) :=
  (lowerUniGL K).subgroupOf (SU (unitaryInvolution K 2 n) 4)

@[expose] noncomputable def UpperU (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Subgroup (SU (unitaryInvolution K 2 n) 4) :=
  (upperUniGL K).subgroupOf (SU (unitaryInvolution K 2 n) 4)

theorem mem_LowerU {n : ℕ} {g : SU (unitaryInvolution K 2 n) 4} :
    g ∈ LowerU K n ↔ IsLowerUni ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  Subgroup.mem_subgroupOf

theorem mem_UpperU {n : ℕ} {g : SU (unitaryInvolution K 2 n) 4} :
    g ∈ UpperU K n ↔ IsUpperUni ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  Subgroup.mem_subgroupOf

theorem jSU_conj_val (n : ℕ) (g : SU (unitaryInvolution K 2 n) 4) :
    ((jSU K n * g * (jSU K n)⁻¹ : SU (unitaryInvolution K 2 n) 4) : GL (Fin 4) K) =
      jGL K * (g : GL (Fin 4) K) * jGL K := by
  have e : ((jSU K n : SU (unitaryInvolution K 2 n) 4) : GL (Fin 4) K) = jGL K := rfl
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, e, jGL_inv]

theorem conj_mem_UpperU_of_mem_LowerU {n : ℕ} {g : SU (unitaryInvolution K 2 n) 4}
    (hg : g ∈ LowerU K n) : jSU K n * g * (jSU K n)⁻¹ ∈ UpperU K n := by
  rw [mem_UpperU, jSU_conj_val, jGL_conj_val]
  exact isUpperUni_J_mul_mul_J (mem_LowerU.mp hg)

theorem mem_LowerU_of_conj_mem_UpperU {n : ℕ} {g : SU (unitaryInvolution K 2 n) 4}
    (h : jSU K n * g * (jSU K n)⁻¹ ∈ UpperU K n) : g ∈ LowerU K n := by
  rw [mem_UpperU, jSU_conj_val, jGL_conj_val] at h
  rw [mem_LowerU]
  have h' := isLowerUni_J_mul_mul_J h
  rwa [J_mul_mul_J_mul_J_mul] at h'

end Subgroups

end CFSG.HardMathSupport.U4FF
