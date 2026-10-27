module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG.Open
open scoped Matrix

variable {F : Type} [Field F]

@[expose] def uniDescAdj (bar : F →+* F) (M : Matrix (Fin 4) (Fin 4) F) : Matrix (Fin 4) (Fin 4) F :=
  (M.map bar)ᵀ

theorem uniDescAdj_mul (bar : F →+* F) (A B : Matrix (Fin 4) (Fin 4) F) :
    uniDescAdj bar (A * B) = uniDescAdj bar B * uniDescAdj bar A := by
  rw [uniDescAdj, uniDescAdj, uniDescAdj, Matrix.map_mul, Matrix.transpose_mul]

theorem uniDescAdj_one (bar : F →+* F) : uniDescAdj bar (1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [uniDescAdj, Matrix.map_one _ (map_zero bar) (map_one bar), Matrix.transpose_one]

theorem uniDescAdj_uniDescAdj (bar : F →+* F) (hbb : ∀ x, bar (bar x) = x)
    (A : Matrix (Fin 4) (Fin 4) F) : uniDescAdj bar (uniDescAdj bar A) = A := by
  ext i j
  simp [uniDescAdj, hbb]

theorem uniDescAdj_eq_transpose (bar : F →+* F) {Y : Matrix (Fin 4) (Fin 4) F} (hY : Y.map bar = Y) :
    uniDescAdj bar Y = Yᵀ := by
  rw [uniDescAdj, hY]

theorem uniDesc_mem_statedSU_iff {q : ℕ} (bar : F →+* F) (hbar : ∀ x, bar x = x ^ q)
    (hbb : ∀ x, bar (bar x) = x) (A : GL (Fin 4) F) :
    A ∈ StatedSU 4 q F ↔ (A : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
  have hmap : ∀ M : Matrix (Fin 4) (Fin 4) F, M.map (· ^ q) = M.map bar := by
    intro M; ext i j; simp [hbar]
  constructor
  · intro hA
    induction hA using Subgroup.closure_induction with
    | mem A hA =>
      obtain ⟨hd, hu⟩ := hA
      refine ⟨hd, ?_⟩
      rw [uniDescAdj, ← hmap]
      exact hu
    | one => simp [uniDescAdj_one]
    | mul A B _ _ hA hB =>
      refine ⟨by simp [Matrix.det_mul, hA.1, hB.1], ?_⟩
      rw [Units.val_mul, uniDescAdj_mul]
      calc uniDescAdj bar (B : Matrix (Fin 4) (Fin 4) F) *
            uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) *
            ((A : Matrix (Fin 4) (Fin 4) F) * B)
          = uniDescAdj bar (B : Matrix (Fin 4) (Fin 4) F) *
            (uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)) * B := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hA.2, Matrix.mul_one, hB.2]
    | inv A _ hA =>
      have h1 : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) := by
        calc ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
            = (uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) * A) *
                ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
              rw [hA.2, Matrix.one_mul]
          _ = uniDescAdj bar (A : Matrix (Fin 4) (Fin 4) F) := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      refine ⟨?_, ?_⟩
      · have : (A : Matrix (Fin 4) (Fin 4) F).det *
            ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det = 1 := by
          rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
        rw [hA.1, one_mul] at this
        exact this
      · rw [h1, uniDescAdj_uniDescAdj bar hbb]
        exact mul_eq_one_comm.1 hA.2
  · rintro ⟨hd, hu⟩
    refine Subgroup.subset_closure ⟨hd, ?_⟩
    rw [hmap]
    exact hu

theorem uniDesc_adj_iff (bar : F →+* F) {P Pi K Y : Matrix (Fin 4) (Fin 4) F}
    (hPPi : P * Pi = 1) (hKP : K * P = P * Y) (hY : Y.map bar = Y) :
    uniDescAdj bar K * K = 1 ↔ Yᵀ * (uniDescAdj bar P * P) * Y = uniDescAdj bar P * P := by
  have key : Yᵀ * (uniDescAdj bar P * P) * Y = uniDescAdj bar P * (uniDescAdj bar K * K) * P := by
    calc Yᵀ * (uniDescAdj bar P * P) * Y
        = uniDescAdj bar Y * uniDescAdj bar P * (P * Y) := by
          rw [uniDescAdj_eq_transpose bar hY]; simp only [Matrix.mul_assoc]
      _ = uniDescAdj bar (P * Y) * (P * Y) := by rw [uniDescAdj_mul]
      _ = uniDescAdj bar (K * P) * (K * P) := by rw [hKP]
      _ = uniDescAdj bar P * (uniDescAdj bar K * K) * P := by
          rw [uniDescAdj_mul]; simp only [Matrix.mul_assoc]
  rw [key]
  constructor
  · intro h
    rw [h, Matrix.mul_one]
  · intro h
    have h1 : uniDescAdj bar Pi * (uniDescAdj bar P * (uniDescAdj bar K * K) * P) * Pi =
        uniDescAdj bar Pi * (uniDescAdj bar P * P) * Pi := by rw [h]
    have hA : uniDescAdj bar Pi * uniDescAdj bar P = 1 := by
      rw [← uniDescAdj_mul, hPPi, uniDescAdj_one]
    calc uniDescAdj bar K * K
        = uniDescAdj bar Pi * (uniDescAdj bar P * (uniDescAdj bar K * K) * P) * Pi := by
          calc uniDescAdj bar K * K
              = (uniDescAdj bar Pi * uniDescAdj bar P) * (uniDescAdj bar K * K) * (P * Pi) := by
                rw [hA, hPPi, Matrix.one_mul, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]
      _ = uniDescAdj bar Pi * (uniDescAdj bar P * P) * Pi := h1
      _ = 1 := by
          calc uniDescAdj bar Pi * (uniDescAdj bar P * P) * Pi
              = (uniDescAdj bar Pi * uniDescAdj bar P) * (P * Pi) := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hA, hPPi, Matrix.mul_one]

end CFSG.GH74.Generic.S1.Exo
