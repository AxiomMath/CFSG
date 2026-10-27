module

public import CFSG.ClassicalInvolution.Q3.Q3MFOU4Gram

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem map_mul_map_eq_one {A Ai : Matrix (Fin 4) (Fin 4) K} (h : A * Ai = 1) :
    A.map σ * Ai.map σ = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero σ) (map_one σ)]

theorem unitary_conj_of_gram {A Ai Y Ω : Matrix (Fin 4) (Fin 4) K} {c : K} (hAAi : A * Ai = 1)
    (hgram : (A.map σ)ᵀ * A = c • Ω) (hY : (Y.map σ)ᵀ * Ω * Y = Ω) :
    ((A * Y * Ai).map σ)ᵀ * (A * Y * Ai) = 1 := by
  have h1 : (Ai.map σ)ᵀ * (A.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, map_mul_map_eq_one σ hAAi, Matrix.transpose_one]
  calc ((A * Y * Ai).map σ)ᵀ * (A * Y * Ai)
      = (Ai.map σ)ᵀ * ((Y.map σ)ᵀ * ((A.map σ)ᵀ * A)) * Y * Ai := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Ai.map σ)ᵀ * ((Y.map σ)ᵀ * (c • Ω)) * Y * Ai := by rw [hgram]
    _ = c • ((Ai.map σ)ᵀ * ((Y.map σ)ᵀ * Ω * Y) * Ai) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = c • ((Ai.map σ)ᵀ * Ω * Ai) := by rw [hY]
    _ = (Ai.map σ)ᵀ * (c • Ω) * Ai := by simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = (Ai.map σ)ᵀ * ((A.map σ)ᵀ * A) * Ai := by rw [hgram]
    _ = ((Ai.map σ)ᵀ * (A.map σ)ᵀ) * (A * Ai) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, hAAi, Matrix.one_mul]

theorem map_conj_eq_of_comm {A Ai X G : Matrix (Fin 4) (Fin 4) K} {ζ : K} (hAAi : A * Ai = 1)
    (hAiA : Ai * A = 1) (htwist : ζ • (G * A.map σ) = A) (hGX : G * X.map σ = X * G) :
    (Ai * X * A).map σ = Ai * X * A := by
  have hBmBi := map_mul_map_eq_one σ hAAi
  have h1 : A * Ai.map σ = ζ • G := by
    calc A * Ai.map σ = (ζ • (G * A.map σ)) * Ai.map σ := by rw [htwist]
      _ = ζ • (G * (A.map σ * Ai.map σ)) := by simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = ζ • G := by rw [hBmBi, Matrix.mul_one]
  have h2 : A * (Ai * X * A).map σ = X * A := by
    calc A * (Ai * X * A).map σ = (A * Ai.map σ) * X.map σ * A.map σ := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = ζ • (G * X.map σ) * A.map σ := by rw [h1]; simp only [Matrix.smul_mul]
      _ = ζ • (X * G) * A.map σ := by rw [hGX]
      _ = X * (ζ • (G * A.map σ)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      _ = X * A := by rw [htwist]
  calc (Ai * X * A).map σ = Ai * (A * (Ai * X * A).map σ) := by
        rw [← Matrix.mul_assoc, hAiA, Matrix.one_mul]
    _ = Ai * (X * A) := by rw [h2]
    _ = Ai * X * A := by rw [Matrix.mul_assoc]

theorem comm_conj_of_map_eq {A Ai Y G : Matrix (Fin 4) (Fin 4) K} {ζ : K} (hζ : ζ ≠ 0)
    (hAAi : A * Ai = 1) (hAiA : Ai * A = 1) (htwist : ζ • (G * A.map σ) = A)
    (hY : Y.map σ = Y) : G * (A * Y * Ai).map σ = (A * Y * Ai) * G := by
  have hBmBi := map_mul_map_eq_one σ hAAi
  have hGBm : G * A.map σ = ζ⁻¹ • A := by
    calc G * A.map σ = ζ⁻¹ • (ζ • (G * A.map σ)) := by rw [smul_smul, inv_mul_cancel₀ hζ, one_smul]
      _ = ζ⁻¹ • A := by rw [htwist]
  have hAiG : Ai * G = ζ⁻¹ • Ai.map σ := by
    have h1 : ζ • (Ai * G) = Ai.map σ := by
      calc ζ • (Ai * G) = ζ • (Ai * G * (A.map σ * Ai.map σ)) := by
            rw [hBmBi, Matrix.mul_one]
        _ = Ai * (ζ • (G * A.map σ)) * Ai.map σ := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = Ai * A * Ai.map σ := by rw [htwist]
        _ = Ai.map σ := by rw [hAiA, Matrix.one_mul]
    calc Ai * G = ζ⁻¹ • (ζ • (Ai * G)) := by rw [smul_smul, inv_mul_cancel₀ hζ, one_smul]
      _ = ζ⁻¹ • Ai.map σ := by rw [h1]
  calc G * (A * Y * Ai).map σ = (G * A.map σ) * Y.map σ * Ai.map σ := by
        simp only [Matrix.map_mul, Matrix.mul_assoc]
    _ = ζ⁻¹ • (A * Y * Ai.map σ) := by
        rw [hGBm, hY]
        simp only [Matrix.smul_mul]
    _ = A * Y * (Ai * G) := by
        rw [hAiG]
        simp only [Matrix.mul_smul]
    _ = (A * Y * Ai) * G := by simp only [Matrix.mul_assoc]

theorem gram_conj_of_unitary {A Ai X Y : Matrix (Fin 4) (Fin 4) K} (hAAi : A * Ai = 1)
    (hX : (X.map σ)ᵀ * X = 1) (hYdef : Y = Ai * X * A) :
    (Y.map σ)ᵀ * ((A.map σ)ᵀ * A) * Y = (A.map σ)ᵀ * A := by
  have h1 : (Ai.map σ)ᵀ * (A.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, map_mul_map_eq_one σ hAAi, Matrix.transpose_one]
  calc (Y.map σ)ᵀ * ((A.map σ)ᵀ * A) * Y
      = (A.map σ)ᵀ * (X.map σ)ᵀ * ((Ai.map σ)ᵀ * (A.map σ)ᵀ) * (A * Ai) * X * A := by
        rw [hYdef]
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (A.map σ)ᵀ * ((X.map σ)ᵀ * X) * A := by
        rw [h1, hAAi]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (A.map σ)ᵀ * A := by rw [hX, Matrix.mul_one]

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
