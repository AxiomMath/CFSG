module

public import CFSG.ClassicalInvolution.Models.LinearFrames.Signs
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Models

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockIdx blockMat_apply rotMat
  diagonal_mul_blockMat_mul_diagonal)

variable {K : Type} [Field K] {n : ℕ}

theorem diagonal_conj_blockMat_two (hn : 2 ≤ n) {d : Fin n → K} (hd : ∀ a, d a * d a = 1)
    (A : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal d * blockMat n 0 A * Matrix.diagonal d =
      blockMat n 0 (Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩] * A *
        Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩]) := by
  rw [diagonal_mul_blockMat_mul_diagonal (by omega : 0 + 2 ≤ n) d d hd]
  have hdd : (fun x : Fin 2 => d (blockIdx 0 (by omega : 0 + 2 ≤ n) x)) =
      ![d ⟨0, by omega⟩, d ⟨1, by omega⟩] := by
    funext x
    fin_cases x <;> rfl
  rw [hdd]

theorem diagonal_conj_blockMat_three (hn : 3 ≤ n) {d : Fin n → K} (hd : ∀ a, d a * d a = 1)
    (A : Matrix (Fin 3) (Fin 3) K) :
    Matrix.diagonal d * blockMat n 0 A * Matrix.diagonal d =
      blockMat n 0 (Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩, d ⟨2, by omega⟩] * A *
        Matrix.diagonal ![d ⟨0, by omega⟩, d ⟨1, by omega⟩, d ⟨2, by omega⟩]) := by
  rw [diagonal_mul_blockMat_mul_diagonal (by omega : 0 + 3 ≤ n) d d hd]
  have hdd : (fun x : Fin 3 => d (blockIdx 0 (by omega : 0 + 3 ≤ n) x)) =
      ![d ⟨0, by omega⟩, d ⟨1, by omega⟩, d ⟨2, by omega⟩] := by
    funext x
    fin_cases x <;> rfl
  rw [hdd]

@[expose] def signUnit (x : K) (hx : x * x = 1) : Kˣ := ⟨x, x, hx, hx⟩

theorem coe_signUnit (x : K) (hx : x * x = 1) : ((signUnit x hx : Kˣ) : K) = x := rfl

theorem coe_signUnit_inv (x : K) (hx : x * x = 1) : (((signUnit x hx)⁻¹ : Kˣ) : K) = x := rfl

theorem diagonal_two_conj_self {a : K} (ha : a * a = 1) (s : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal ![a, a] * s * Matrix.diagonal ![a, a] = s := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination (s _ _) * ha

theorem diagonal_three_conj_eq {e₀ e₁ e₂ : K} (h22 : e₂ * e₂ = 1) (x : Matrix (Fin 3) (Fin 3) K) :
    Matrix.diagonal ![e₀, e₁, e₂] * x * Matrix.diagonal ![e₀, e₁, e₂] =
      Matrix.diagonal ![e₀ * e₂, e₁ * e₂, 1] * x * Matrix.diagonal ![e₀ * e₂, e₁ * e₂, 1] := by
  have hD : Matrix.diagonal ![e₀ * e₂, e₁ * e₂, (1 : K)] =
      e₂ • Matrix.diagonal ![e₀, e₁, e₂] := by
    ext i j
    rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp [h22] <;> ring
    · simp [hij]
  rw [hD]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h22, one_smul]

theorem isMonomialFor_blockMat_rotMat (hn : 2 ≤ n) :
    IsMonomialFor (blockMat n 0 (rotMat : Matrix (Fin 2) (Fin 2) K))
      (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < n := by omega
  intro k
  rw [Matrix.mulVec_single_one]
  by_cases hk0 : k.val = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    obtain rfl : k = ⟨0, hn0⟩ := Fin.ext hk0
    ext a
    rw [Matrix.col_apply, blockMat_apply, Equiv.swap_apply_left]
    by_cases ha0 : a.val = 0
    · obtain rfl : a = ⟨0, hn0⟩ := Fin.ext ha0
      simp [rotMat]
    · by_cases ha1 : a.val = 1
      · obtain rfl : a = ⟨1, hn1⟩ := Fin.ext ha1
        simp [rotMat]
      · rw [dite_eq_right (by simp; omega)]
        simp [Fin.ext_iff, ha0, ha1]
  · by_cases hk1 : k.val = 1
    · refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
      obtain rfl : k = ⟨1, hn1⟩ := Fin.ext hk1
      ext a
      rw [Matrix.col_apply, blockMat_apply, Equiv.swap_apply_right]
      by_cases ha0 : a.val = 0
      · obtain rfl : a = ⟨0, hn0⟩ := Fin.ext ha0
        simp [rotMat]
      · by_cases ha1 : a.val = 1
        · obtain rfl : a = ⟨1, hn1⟩ := Fin.ext ha1
          simp [rotMat]
        · rw [dite_eq_right (by simp; omega)]
          simp [Fin.ext_iff, ha0, ha1]
    · refine ⟨1, one_ne_zero, ?_⟩
      have hs : Equiv.swap (⟨0, hn0⟩ : Fin n) ⟨1, hn1⟩ k = k :=
        Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)
      ext a
      rw [Matrix.col_apply, blockMat_apply, hs]
      rw [dite_eq_right (by simp; omega)]
      simp [Pi.single_apply, Matrix.one_apply]

end CFSG.ClassicalInvolution.Models
