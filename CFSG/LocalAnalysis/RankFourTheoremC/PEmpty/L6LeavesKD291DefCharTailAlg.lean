module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix

section Algebra

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

theorem mulParam_single (i₀ : Fin r) (v v' : A) (C C' : Matrix (Fin r) (Fin r) K) :
    mulParam qA (Pi.single i₀ v) (Pi.single i₀ v') C C' = C + C' := by
  ext i j
  simp only [mulParam, Matrix.sub_apply, Matrix.add_apply, sMat, crossMat, of_apply, Pi.add_apply]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    rw [QuadraticMap.map_add qA]
    ring
  · by_cases hlt : i < j
    · simp only [hij, hlt, ↓reduceIte]
      rw [polar_add_left, polar_add_right, polar_add_right]
      by_cases hi : i = i₀
      · have hj : j ≠ i₀ := fun h => hij (hi.trans h.symm)
        simp [Pi.single_apply, hj]
      · simp [Pi.single_apply, hi]
    · simp only [hij, hlt, ↓reduceIte]
      by_cases hi : i = i₀
      · have hj : j ≠ i₀ := fun h => hij (hi.trans h.symm)
        simp [Pi.single_apply, hj]
      · simp [Pi.single_apply, hi]

theorem uMap_single_mul (i₀ : Fin r) (v v' : A) (C C' : Matrix (Fin r) (Fin r) K) :
    uMap qA (Pi.single i₀ v) C * uMap qA (Pi.single i₀ v') C' =
      uMap qA (Pi.single i₀ (v + v')) (C + C') := by
  rw [uMap_mul_uMap, ← Pi.single_add, mulParam_single]

theorem mulParam_zero_left (L : Fin r → A) (E C : Matrix (Fin r) (Fin r) K) :
    mulParam qA 0 L E C = E + C := by
  simp only [mulParam, sMat_zero, zero_add, crossMat]
  have : (Matrix.of fun i j => polar qA ((0 : Fin r → A) i) (L j) : Matrix (Fin r) (Fin r) K) =
      0 := by
    ext i j
    simp
  rw [this]
  abel

theorem mulParam_zero_right (L : Fin r → A) (C E : Matrix (Fin r) (Fin r) K) :
    mulParam qA L 0 C E = C + E := by
  simp only [mulParam, sMat_zero, add_zero, crossMat]
  have : (Matrix.of fun i j => polar qA (L i) ((0 : Fin r → A) j) : Matrix (Fin r) (Fin r) K) =
      0 := by
    ext i j
    simp
  rw [this]
  abel

theorem uMap_zero_mul_eq (L : Fin r → A) (E C : Matrix (Fin r) (Fin r) K) :
    uMap qA 0 E * uMap qA L C = uMap qA L (E + C) := by
  rw [uMap_mul_uMap, zero_add, mulParam_zero_left]

theorem uMap_mul_zero_eq (L : Fin r → A) (C E : Matrix (Fin r) (Fin r) K) :
    uMap qA L C * uMap qA 0 E = uMap qA L (C + E) := by
  rw [uMap_mul_uMap, add_zero, mulParam_zero_right]

theorem uMap_zero_comm (L : Fin r → A) (E C : Matrix (Fin r) (Fin r) K) :
    uMap qA 0 E * uMap qA L C = uMap qA L C * uMap qA 0 E := by
  rw [uMap_zero_mul_eq, uMap_mul_zero_eq, add_comm]

theorem uMap_comm_cross (L L' : Fin r → A) (C C' : Matrix (Fin r) (Fin r) K) :
    uMap qA L' C' * uMap qA L C =
      uMap qA L C * uMap qA L' C' * uMap qA 0 (crossMat qA L L' - crossMat qA L' L) := by
  rw [uMap_mul_uMap, uMap_mul_uMap, uMap_mul_zero_eq, add_comm L' L]
  congr 1
  simp only [mulParam]
  abel

theorem uMap_single_inv (i₀ : Fin r) (v : A) (C : Matrix (Fin r) (Fin r) K) :
    (uMap qA (Pi.single i₀ v) C)⁻¹ = uMap qA (Pi.single i₀ (-v)) (-C) := by
  rw [inv_eq_iff_mul_eq_one, uMap_single_mul, add_neg_cancel, add_neg_cancel, Pi.single_zero]
  exact uMap_zero_zero

theorem uMap_single_pow (i₀ : Fin r) (v : A) (C : Matrix (Fin r) (Fin r) K) (n : ℕ) :
    (uMap qA (Pi.single i₀ v) C) ^ n = uMap qA (Pi.single i₀ (n • v)) (n • C) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_nsmul, zero_nsmul, Pi.single_zero]
    exact uMap_zero_zero.symm
  | succ n ih =>
    rw [pow_succ, ih, uMap_single_mul, succ_nsmul, succ_nsmul]

theorem sMat_single (i₀ : Fin r) (v : A) :
    sMat qA (Pi.single i₀ v) = Matrix.single i₀ i₀ (-qA v) := by
  ext i j
  simp only [sMat, of_apply, Matrix.single_apply]
  by_cases hi : i = i₀
  · subst hi
    by_cases hj : j = i
    · subst hj
      simp
    · have hij : i ≠ j := fun h => hj h.symm
      have h2 : ¬ (i = i ∧ i = j) := fun h => hij h.2
      have hz : (Pi.single i v : Fin r → A) j = 0 := by simp [Pi.single_apply, hj]
      simp [hij, h2, hz]
  · have hz : (Pi.single i₀ v : Fin r → A) i = 0 := by simp [Pi.single_apply, hi]
    have h2 : ¬ (i₀ = i ∧ i₀ = j) := fun h => hi h.1.symm
    have hi' : ¬ i₀ = i := fun h => hi h.symm
    by_cases hij : i = j
    · subst hij
      simp [hi', hz]
    · by_cases hlt : i < j
      · simp [hij, hlt, h2, hz]
      · simp [hij, hlt, h2]

variable {D : GL (Fin r) K}

theorem conjL_single (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {i₀ : Fin r} (hi₀ : (i₀ : ℕ) = 0) (v : A) :
    conjL D (1 : A ≃ₗ[K] A) (Pi.single i₀ v) = Pi.single i₀ v := by
  funext j
  simp only [conjL, Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases hj : j = i₀
  · subst hj
    simp [h1]
  · have hlt : i₀ < j := by
      rw [Fin.lt_def]
      have : (j : ℕ) ≠ i₀ := fun h => hj (Fin.ext h)
      omega
    simp [hD hlt, hj]

theorem conjL_zero : conjL D (1 : A ≃ₗ[K] A) (0 : Fin r → A) = 0 := by
  funext j
  simp [conjL]

theorem conj_single_single (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {i₀ : Fin r} (hi₀ : (i₀ : ℕ) = 0) (x : K) :
    (D : Matrix (Fin r) (Fin r) K) * Matrix.single i₀ i₀ x * (D : Matrix (Fin r) (Fin r) K)ᵀ =
      Matrix.single i₀ i₀ x := by
  have hcol : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i₀ = if i₀ = i then 1 else 0 := by
    intro i
    by_cases hi : i₀ = i
    · subst hi
      simp [h1]
    · have hlt : i₀ < i := by
        rw [Fin.lt_def]
        have : (i₀ : ℕ) ≠ i := fun h => hi (Fin.ext h)
        omega
      simp [hD hlt, hi]
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i₀]
  · rw [Matrix.mul_single_apply_same, Matrix.transpose_apply, hcol i, hcol j]
    simp only [Matrix.single_apply]
    by_cases hi : i₀ = i <;> by_cases hj : i₀ = j <;> simp [hi, hj]
  · intro l _ hl
    rw [Matrix.mul_single_apply_of_ne x i₀ i₀ i l hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem conj_uMap_single (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {i₀ : Fin r} (hi₀ : (i₀ : ℕ) = 0) (v : A)
    (C : Matrix (Fin r) (Fin r) K) :
    dMap D (1 : A ≃ₗ[K] A) * uMap qA (Pi.single i₀ v) C * (dMap D (1 : A ≃ₗ[K] A))⁻¹ =
      uMap qA (Pi.single i₀ v) ((D : Matrix (Fin r) (Fin r) K) * C *
        (D : Matrix (Fin r) (Fin r) K)ᵀ) := by
  rw [dMap_conj_uMap (one_mem _) D (Pi.single i₀ v) C, conjL_single hD h1 hi₀, conjC,
    conjL_single hD h1 hi₀, sMat_single, mul_add, add_mul, conj_single_single hD h1 hi₀]
  congr 1
  abel

theorem conj_uMap_zero (E : Matrix (Fin r) (Fin r) K) :
    dMap D (1 : A ≃ₗ[K] A) * uMap qA 0 E * (dMap D (1 : A ≃ₗ[K] A))⁻¹ =
      uMap qA 0 ((D : Matrix (Fin r) (Fin r) K) * E * (D : Matrix (Fin r) (Fin r) K)ᵀ) := by
  rw [dMap_conj_uMap (one_mem _) D 0 E, conjL_zero, conjC, conjL_zero, sMat_zero]
  simp

theorem commutator_formula (hD : (D : Matrix (Fin r) (Fin r) K).IsUpperTriangular)
    (h1 : ∀ i, (D : Matrix (Fin r) (Fin r) K) i i = 1) {i₀ : Fin r} (hi₀ : (i₀ : ℕ) = 0) (v : A)
    (C : Matrix (Fin r) (Fin r) K) (L' : Fin r → A) (C' : Matrix (Fin r) (Fin r) K) :
    (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C') * uMap qA (Pi.single i₀ v) C *
        (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C')⁻¹ * (uMap qA (Pi.single i₀ v) C)⁻¹ =
      uMap qA 0 ((D : Matrix (Fin r) (Fin r) K) *
        (crossMat qA (Pi.single i₀ v) L' - crossMat qA L' (Pi.single i₀ v) + C) *
        (D : Matrix (Fin r) (Fin r) K)ᵀ - C) := by
  set L : Fin r → A := Pi.single i₀ v with hL
  set E₁ : Matrix (Fin r) (Fin r) K := crossMat qA L L' - crossMat qA L' L with hE₁
  have hwa : uMap qA L' C' * uMap qA L C * (uMap qA L' C')⁻¹ = uMap qA L C * uMap qA 0 E₁ := by
    rw [uMap_comm_cross L L' C C', ← hE₁]
    have hzw : uMap qA 0 E₁ * uMap qA L' C' = uMap qA L' C' * uMap qA 0 E₁ :=
      uMap_zero_comm L' E₁ C'
    calc uMap qA L C * uMap qA L' C' * uMap qA 0 E₁ * (uMap qA L' C')⁻¹
        = uMap qA L C * (uMap qA L' C' * uMap qA 0 E₁) * (uMap qA L' C')⁻¹ := by
          rw [mul_assoc (uMap qA L C)]
      _ = uMap qA L C * (uMap qA 0 E₁ * uMap qA L' C') * (uMap qA L' C')⁻¹ := by rw [hzw]
      _ = uMap qA L C * uMap qA 0 E₁ := by group
  have hda := conj_uMap_single (qA := qA) hD h1 hi₀ v C
  have hdz := conj_uMap_zero (qA := qA) (D := D) E₁
  have step : (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C') * uMap qA L C *
      (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C')⁻¹ =
      uMap qA L ((D : Matrix (Fin r) (Fin r) K) * C * (D : Matrix (Fin r) (Fin r) K)ᵀ +
        (D : Matrix (Fin r) (Fin r) K) * E₁ * (D : Matrix (Fin r) (Fin r) K)ᵀ) := by
    calc (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C') * uMap qA L C *
          (dMap D (1 : A ≃ₗ[K] A) * uMap qA L' C')⁻¹
        = dMap D (1 : A ≃ₗ[K] A) * (uMap qA L' C' * uMap qA L C * (uMap qA L' C')⁻¹) *
            (dMap D (1 : A ≃ₗ[K] A))⁻¹ := by group
      _ = dMap D (1 : A ≃ₗ[K] A) * (uMap qA L C * uMap qA 0 E₁) *
            (dMap D (1 : A ≃ₗ[K] A))⁻¹ := by rw [hwa]
      _ = (dMap D (1 : A ≃ₗ[K] A) * uMap qA L C * (dMap D (1 : A ≃ₗ[K] A))⁻¹) *
            (dMap D (1 : A ≃ₗ[K] A) * uMap qA 0 E₁ * (dMap D (1 : A ≃ₗ[K] A))⁻¹) := by group
      _ = uMap qA L ((D : Matrix (Fin r) (Fin r) K) * C * (D : Matrix (Fin r) (Fin r) K)ᵀ) *
            uMap qA 0 ((D : Matrix (Fin r) (Fin r) K) * E₁ * (D : Matrix (Fin r) (Fin r) K)ᵀ) := by
          rw [hda, hdz]
      _ = _ := uMap_mul_zero_eq _ _ _
  rw [step, mul_inv_eq_iff_eq_mul, uMap_zero_mul_eq]
  congr 1
  simp only [mul_add, add_mul]
  abel

end Algebra

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC
