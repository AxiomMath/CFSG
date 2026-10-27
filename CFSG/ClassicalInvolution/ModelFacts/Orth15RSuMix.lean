module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15RSuAlg

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu

open Matrix

variable {K : Type} [Field K]

@[expose] def diag4 (s w : K) : Matrix (Fin 4) (Fin 4) K :=
  !![s, 0, 0, 0; 0, s, 0, 0; 0, 0, w, 0; 0, 0, 0, w]

@[expose] def MixProp (M : Matrix (Fin 4) (Fin 4) K) : Prop :=
  ∀ s w : K, s ≠ 0 → w ≠ 0 → ∀ z : K, diag4 s w * M = z • (M * diag4 s w) → s = w

theorem mixProp_of_conj {Y Yi M M₀ : Matrix (Fin 4) (Fin 4) K} (hYiY : Yi * Y = 1)
    (hD : ∀ s w : K, diag4 s w * Y = Y * Matrix.diagonal ![s, w, s, w])
    (hM : M * Y = Y * M₀)
    (h₀ : ∀ s w : K, s ≠ 0 → w ≠ 0 → ∀ z : K,
      Matrix.diagonal ![s, w, s, w] * M₀ = z • (M₀ * Matrix.diagonal ![s, w, s, w]) → s = w) :
    MixProp M := by
  intro s w hs hw z h
  apply h₀ s w hs hw z
  have h1 : Y * (Matrix.diagonal ![s, w, s, w] * M₀) =
      Y * (z • (M₀ * Matrix.diagonal ![s, w, s, w])) := by
    calc Y * (Matrix.diagonal ![s, w, s, w] * M₀)
        = (Y * Matrix.diagonal ![s, w, s, w]) * M₀ := by rw [Matrix.mul_assoc]
      _ = (diag4 s w * Y) * M₀ := by rw [hD]
      _ = diag4 s w * (Y * M₀) := by rw [Matrix.mul_assoc]
      _ = diag4 s w * (M * Y) := by rw [hM]
      _ = (diag4 s w * M) * Y := by rw [Matrix.mul_assoc]
      _ = (z • (M * diag4 s w)) * Y := by rw [h]
      _ = z • (M * (diag4 s w * Y)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = z • (M * (Y * Matrix.diagonal ![s, w, s, w])) := by rw [hD]
      _ = z • ((M * Y) * Matrix.diagonal ![s, w, s, w]) := by rw [Matrix.mul_assoc]
      _ = z • ((Y * M₀) * Matrix.diagonal ![s, w, s, w]) := by rw [hM]
      _ = Y * (z • (M₀ * Matrix.diagonal ![s, w, s, w])) := by
          rw [Matrix.mul_assoc, Matrix.mul_smul]
  calc Matrix.diagonal ![s, w, s, w] * M₀
      = (Yi * Y) * (Matrix.diagonal ![s, w, s, w] * M₀) := by rw [hYiY, Matrix.one_mul]
    _ = Yi * (Y * (Matrix.diagonal ![s, w, s, w] * M₀)) := by rw [Matrix.mul_assoc]
    _ = Yi * (Y * (z • (M₀ * Matrix.diagonal ![s, w, s, w]))) := by rw [h1]
    _ = (Yi * Y) * (z • (M₀ * Matrix.diagonal ![s, w, s, w])) := by rw [← Matrix.mul_assoc]
    _ = z • (M₀ * Matrix.diagonal ![s, w, s, w]) := by rw [hYiY, Matrix.one_mul]

theorem diag4_eq_diagonal (s w : K) : diag4 s w = Matrix.diagonal ![s, s, w, w] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diag4]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSu
