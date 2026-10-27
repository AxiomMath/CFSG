module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Mat

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

section Gram

variable {K : Type} [Field K]

@[expose] def Mmat (ζ ι m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![ζ * m, -(ζ * m * ι), 0, 0; 1, ι, 0, 0; 0, 0, ζ * n, -(ζ * n * ι); 0, 0, 1, ι]

@[expose] def Gmat (m n : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]

@[expose] def Omg (R : Type) [Ring R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

theorem gram_Mmat (σ : K ≃+* K) {ζ ι m n : K} (hιb : σ ι = -ι) (hζ : σ ζ * ζ = -1)
    (hm : σ m * m = 1) (hn : σ n * n = 1) (h3 : (3 : K) = 0) :
    ((Mmat ζ ι m n).map σ)ᵀ * Mmat ζ ι m n = ι • (Omg K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mmat, Omg, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
      Matrix.map_apply, hιb] <;> grind

theorem twist_Mmat (σ : K ≃+* K) {ζ ι m n : K} (hιb : σ ι = -ι) (hζ : σ ζ * ζ = -1)
    (hm : σ m * m = 1) (hn : σ n * n = 1) (h3 : (3 : K) = 0) :
    ζ • (Gmat m n * (Mmat ζ ι m n).map σ) = Mmat ζ ι m n := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.map_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [Mmat, Gmat, hιb] <;> grind

theorem det_Mmat (ζ ι m n : K) :
    (Mmat ζ ι m n).det = (2 * ζ * m * ι) * (2 * ζ * n * ι) := by
  rw [Mmat, det_blockDiag4]
  ring

theorem det_Mmat_ne_zero (h2 : (2 : K) ≠ 0) {ζ ι m n : K} (hζ : ζ ≠ 0) (hι : ι ≠ 0) (hm : m ≠ 0)
    (hn : n ≠ 0) : (Mmat ζ ι m n).det ≠ 0 := by
  rw [det_Mmat]
  exact mul_ne_zero (by simp [h2, hζ, hm, hι]) (by simp [h2, hζ, hn, hι])

end Gram

section Omega

variable {R : Type} [CommRing R]

theorem Omg_mul_self : Omg R * Omg R = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Omg, Matrix.mul_apply, Fin.sum_univ_four]

theorem symp_transpose (y : Matrix (Fin 4) (Fin 4) R) (h : y * Omg R * yᵀ = Omg R) :
    yᵀ * Omg R * y = Omg R := by
  have h1 : (Omg R * y * Omg R) * yᵀ = -1 := by
    calc (Omg R * y * Omg R) * yᵀ = Omg R * (y * Omg R * yᵀ) := by simp only [Matrix.mul_assoc]
      _ = -1 := by rw [h, Omg_mul_self]
  have h2 : yᵀ * (Omg R * y * Omg R) = -1 := by
    have h3 : (-(Omg R * y * Omg R)) * yᵀ = 1 := by
      rw [Matrix.neg_mul, h1, neg_neg]
    have h4 := mul_eq_one_comm.mp h3
    rw [Matrix.mul_neg] at h4
    exact neg_eq_iff_eq_neg.mp h4
  have h5 : -(yᵀ * Omg R * y) = -Omg R := by
    have h6 := congrArg (fun X => X * Omg R) h2
    simp only [Matrix.neg_mul, Matrix.one_mul] at h6
    calc -(yᵀ * Omg R * y) = yᵀ * Omg R * y * (Omg R * Omg R) := by
          rw [Omg_mul_self, Matrix.mul_neg, Matrix.mul_one]
      _ = yᵀ * (Omg R * y * Omg R) * Omg R := by simp only [Matrix.mul_assoc]
      _ = -Omg R := h6
  exact neg_inj.mp h5

end Omega

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
