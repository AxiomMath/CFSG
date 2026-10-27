module

public import CFSG.LieType.Universal.Unitary.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary

section Matrices

variable {F : Type} [Field F]

@[expose] def tMat (q : ℕ) (μ : Fˣ) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.diagonal ![(μ : F), ((μ ^ (q - 1) : Fˣ) : F), (((μ ^ q)⁻¹ : Fˣ) : F)]

theorem tMat_mul (q : ℕ) (μ ν : Fˣ) : tMat q (μ * ν) = tMat q μ * tMat q ν := by
  unfold tMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp [mul_pow]
  all_goals exact mul_comm _ _

theorem tMat_one (q : ℕ) : tMat q (1 : Fˣ) = (1 : Matrix (Fin 3) (Fin 3) F) := by
  unfold tMat
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

@[expose] def tGL (q : ℕ) (μ : Fˣ) : GL (Fin 3) F :=
  ⟨tMat q μ, tMat q μ⁻¹, by rw [← tMat_mul, mul_inv_cancel, tMat_one],
    by rw [← tMat_mul, inv_mul_cancel, tMat_one]⟩

theorem coe_tGL (q : ℕ) (μ : Fˣ) :
    ((tGL q μ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = tMat q μ := rfl

@[expose] def tGLHom (q : ℕ) : Fˣ →* GL (Fin 3) F where
  toFun := tGL q
  map_one' := Units.ext (by simp [coe_tGL, tMat_one])
  map_mul' μ ν := Units.ext (by simp [coe_tGL, tMat_mul])

theorem tGLHom_injective (q : ℕ) : Function.Injective (tGLHom (F := F) q) := by
  intro μ ν h
  have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  exact Units.ext (by simpa [tGLHom, coe_tGL, tMat] using this)

@[expose] def sMat : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem sMat_mul_self : (sMat : Matrix (Fin 3) (Fin 3) F) * sMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_sMat : (sMat : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  simp [sMat, Matrix.det_fin_three]

@[expose] def swapGL : GL (Fin 3) F := ⟨sMat, sMat, sMat_mul_self, sMat_mul_self⟩

theorem sMat_mul_diagonal (a b c : F) :
    (sMat : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![a, b, c] =
      Matrix.diagonal ![c, b, a] * sMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sMat, Matrix.mul_apply, Matrix.diagonal_apply]

theorem unit_pow_sq_sub_one {q : ℕ} (hq : 1 ≤ q) (hq2 : ∀ x : F, x ^ (q ^ 2) = x) (μ : Fˣ) :
    μ ^ (q ^ 2 - 1) = 1 := by
  have hμ : μ ^ (q ^ 2) = μ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hq2 _)
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h : μ ^ (q ^ 2 - 1) * μ = μ := by rw [← pow_succ, Nat.sub_add_cancel hq1]; exact hμ
  simpa using h

theorem tMat_inv_pow {q : ℕ} (hq : 1 ≤ q) (hq2 : ∀ x : F, x ^ (q ^ 2) = x) (μ : Fˣ) :
    tMat q (μ ^ q)⁻¹ = Matrix.diagonal ![(((μ ^ q)⁻¹ : Fˣ) : F), ((μ ^ (q - 1) : Fˣ) : F), (μ : F)] := by
  have hμ1 := unit_pow_sq_sub_one hq hq2 μ
  have hμ : μ ^ (q ^ 2) = μ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hq2 _)
  have e2 : ((μ ^ q)⁻¹) ^ (q - 1) = μ ^ (q - 1) := by
    have h : μ ^ (q * (q - 1)) * μ ^ (q - 1) = 1 := by
      rw [← pow_add, ← hμ1]
      congr 1
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      symm
      apply Nat.sub_eq_of_eq_add
      ring
    rw [inv_pow, ← pow_mul]
    exact inv_eq_of_mul_eq_one_right h
  have e3 : (((μ ^ q)⁻¹) ^ q)⁻¹ = μ := by
    rw [inv_pow, ← pow_mul, inv_inv, ← sq, hμ]
  unfold tMat
  congr 1
  ext i
  fin_cases i
  · rfl
  · simp only [e2]; rfl
  · simp only [e3]; rfl

theorem sMat_mul_tMat {q : ℕ} (hq : 1 ≤ q) (hq2 : ∀ x : F, x ^ (q ^ 2) = x) (μ : Fˣ) :
    (sMat : Matrix (Fin 3) (Fin 3) F) * tMat q μ = tMat q (μ ^ q)⁻¹ * sMat := by
  rw [tMat_inv_pow hq hq2]
  exact sMat_mul_diagonal _ _ _

theorem conjTr_diagonal_antidiag (σ : F ≃+* F) {d₀ d₁ d₂ : F} (h0 : σ d₀ * d₂ = 1)
    (h1 : σ d₁ * d₁ = 1) (h2 : σ d₂ * d₀ = 1) :
    conjTr σ (Matrix.diagonal ![d₀, d₁, d₂]) * antidiag 3 * Matrix.diagonal ![d₀, d₁, d₂] =
      antidiag 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, h0, h1, h2]

section Membership

variable (σ : F ≃+* F) {q : ℕ}

theorem tGL_mem_SU (hq : 1 ≤ q) (hσ : ∀ x, σ x = x ^ q) (hq2 : ∀ x : F, x ^ (q ^ 2) = x)
    (μ : Fˣ) : tGL q μ ∈ SU σ 3 := by
  have hμ : μ ^ (q ^ 2) = μ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hq2 _)
  have hμ1 := unit_pow_sq_sub_one hq hq2 μ
  refine ⟨?_, ?_⟩
  · have h : μ * μ ^ (q - 1) * (μ ^ q)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hq, mul_inv_cancel]
    have := congrArg Units.val h
    simpa [coe_tGL, tMat, Matrix.det_diagonal, Fin.prod_univ_three] using this
  · rw [coe_tGL]
    unfold tMat
    refine conjTr_diagonal_antidiag σ ?_ ?_ ?_
    · show σ (μ : F) * (((μ ^ q)⁻¹ : Fˣ) : F) = 1
      rw [hσ, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · show σ ((μ ^ (q - 1) : Fˣ) : F) * ((μ ^ (q - 1) : Fˣ) : F) = 1
      rw [hσ, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have h : (μ ^ (q - 1)) ^ q * μ ^ (q - 1) = 1 := by
        rw [← pow_mul, ← pow_add, ← hμ1]
        congr 1
        obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        symm
        apply Nat.sub_eq_of_eq_add
        ring
      rw [h, Units.val_one]
    · show σ ((((μ ^ q)⁻¹ : Fˣ)) : F) * (μ : F) = 1
      rw [hσ, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      have h : ((μ ^ q)⁻¹) ^ q * μ = 1 := by
        rw [inv_pow, ← pow_mul, ← sq, hμ, inv_mul_cancel]
      rw [h, Units.val_one]

theorem swapGL_mem_SU : (swapGL : GL (Fin 3) F) ∈ SU σ 3 := by
  refine ⟨det_sMat, ?_⟩
  have hc : conjTr σ (sMat : Matrix (Fin 3) (Fin 3) F) = sMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, sMat]
  show conjTr σ (sMat : Matrix (Fin 3) (Fin 3) F) * antidiag 3 * sMat = antidiag 3
  rw [hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sMat, antidiag, Matrix.mul_apply, Matrix.vecHead, Matrix.vecTail]

end Membership

end Matrices

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
