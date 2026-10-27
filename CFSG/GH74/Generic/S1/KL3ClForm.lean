module

public import CFSG.Assembly.LowTwoRankDefs

public section

open Matrix CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.Generic.S1

section Closure

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem kl3cl_form_closure (J : Matrix ι ι K) (A : GL ι K)
    (hA : A ∈ Subgroup.closure {A : GL ι K | (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J}) :
    (A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K) = J := by
  induction hA using Subgroup.closure_induction with
  | mem A hA => exact hA
  | one => simp
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (B : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ * J * ((A : Matrix ι ι K) * (B : Matrix ι ι K))
        = (B : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) * (B : Matrix ι ι K) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hA, hB]
  | inv A _ hA =>
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = ((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((A : Matrix ι ι K)ᵀ * J * (A : Matrix ι ι K)) *
          ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA]
      _ = (((A⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * (A : Matrix ι ι K)ᵀ) * J *
          ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2]; simp

theorem kl3cl_unitary_closure (φ : K →+* K) (A : GL ι K)
    (hA : A ∈ Subgroup.closure {A : GL ι K | ((A : Matrix ι ι K).map φ)ᵀ * (A : Matrix ι ι K) = 1}) :
    ((A : Matrix ι ι K).map φ)ᵀ * (A : Matrix ι ι K) = 1 := by
  induction hA using Subgroup.closure_induction with
  | mem A hA => exact hA
  | one => simp
  | mul A B _ _ hA hB =>
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((B : Matrix ι ι K).map φ)ᵀ * ((A : Matrix ι ι K).map φ)ᵀ * ((A : Matrix ι ι K) * (B : Matrix ι ι K))
        = ((B : Matrix ι ι K).map φ)ᵀ * (((A : Matrix ι ι K).map φ)ᵀ * (A : Matrix ι ι K)) *
          (B : Matrix ι ι K) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one, hB]
  | inv A _ hA =>
    have h1 : (A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h4 : ((A : Matrix ι ι K).map φ) * (((A⁻¹ : GL ι K) : Matrix ι ι K).map φ) = 1 := by
      rw [← Matrix.map_mul, h1]; simp
    calc (((A⁻¹ : GL ι K) : Matrix ι ι K).map φ)ᵀ * ((A⁻¹ : GL ι K) : Matrix ι ι K)
        = (((A⁻¹ : GL ι K) : Matrix ι ι K).map φ)ᵀ * (((A : Matrix ι ι K).map φ)ᵀ * (A : Matrix ι ι K)) *
          ((A⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hA, Matrix.mul_one]
      _ = (((A : Matrix ι ι K).map φ) * (((A⁻¹ : GL ι K) : Matrix ι ι K).map φ))ᵀ *
          ((A : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) := by
            rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h4, h1]; simp

end Closure

section Models

variable {K : Type} [Field K]

theorem kl3cl_statedSp_form {n : ℕ} (A : GL (Fin n ⊕ Fin n) K) (hA : A ∈ StatedSp n K) :
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.fromBlocks 0 1 (-1) 0 :=
  kl3cl_form_closure _ A hA

theorem kl3cl_statedSU_form {n e p : ℕ} [Fact p.Prime] [CharP K p] (A : GL (Fin n) K)
    (hA : A ∈ StatedSU n (p ^ e) K) :
    ((A : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ e)))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have hExp : ExpChar K p := ExpChar.prime (Fact.out)
  let φ : K →+* K := iterateFrobenius K p e
  have hmap : ∀ M : Matrix (Fin n) (Fin n) K, M.map (· ^ (p ^ e)) = M.map φ := fun M => by
    ext i j; simp [φ, iterateFrobenius_def]
  have hA' : A ∈ Subgroup.closure {B : GL (Fin n) K |
      ((B : Matrix (Fin n) (Fin n) K).map φ)ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1} :=
    Subgroup.closure_mono (fun B hB => by rw [Set.mem_ofPred_eq, ← hmap]; exact hB.2) hA
  rw [hmap]
  exact kl3cl_unitary_closure φ A hA'

end Models

end CFSG.GH74.Generic.S1
