module

public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_comm blockMat_blockMat
  blockMat_injective blockMat_apply_of_not_mem_left swapMat swapMat_mul_self det_swapMat rotMat
  rotMatInv rotMat_mul_rotMatInv rotMatInv_mul_rotMat det_rotMat swapMat_mul_embPair_two
  swapMat_mul_embPair_zero embPair_two_eq_blockMat embPair_zero_eq_blockMat)
open scoped MatrixGroups

section Entries

variable {K : Type} [Field K] {m k l i j : ℕ}

theorem coe_blockSL_three_zero (A : SL(2, K)) :
    ((blockSL K 3 2 0 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem coe_blockSL_three_one (A : SL(2, K)) :
    ((blockSL K 3 2 1 (by omega) A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_blockSL, blockMat_apply]

theorem blockSL_injective (h : i + k ≤ m) : Function.Injective (blockSL K m k i h) := by
  intro A B hAB
  have := congrArg (fun g : SL(m, K) => (g : Matrix (Fin m) (Fin m) K)) hAB
  exact Subtype.ext (blockMat_injective h this)

theorem blockSL_comm (h₁ : i + k ≤ m) (h₂ : j + l ≤ m) (hij : i + k ≤ j ∨ j + l ≤ i)
    (A : SL(k, K)) (B : SL(l, K)) :
    blockSL K m k i h₁ A * blockSL K m l j h₂ B = blockSL K m l j h₂ B * blockSL K m k i h₁ A :=
  Subtype.ext (blockMat_comm hij _ _)

theorem blockSL_comp (h₁ : i + k ≤ m) (h₂ : j + l ≤ k) :
    (blockSL K m k i h₁).comp (blockSL K k l j h₂) = blockSL K m l (i + j) (by omega) :=
  MonoidHom.ext fun _ => Subtype.ext (blockMat_blockMat h₂ _)

theorem blockSL_comp_apply (h₁ : i + k ≤ m) (h₂ : j + l ≤ k) (A : SL(l, K)) :
    blockSL K m k i h₁ (blockSL K k l j h₂ A) = blockSL K m l (i + j) (by omega) A :=
  DFunLike.congr_fun (blockSL_comp h₁ h₂) A

end Entries

section Blocks

variable {K : Type} [Field K]

theorem blockSL2_comm (n : ℕ) (i j : Fin n) (hij : (i : ℕ) + 1 < j) (A B : SL(2, K)) :
    blockSL2 K n i A * blockSL2 K n j B = blockSL2 K n j B * blockSL2 K n i A :=
  blockSL_comm _ _ (Or.inl (by omega)) A B

theorem blockSL3_comp_left (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockSL3 K n i h).comp (blockSL K 3 2 0 (by omega)) = blockSL2 K n i :=
  blockSL_comp _ _

theorem blockSL3_comp_right (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (blockSL3 K n i h).comp (blockSL K 3 2 1 (by omega)) = blockSL2 K n ⟨i + 1, h⟩ :=
  blockSL_comp _ _

theorem blockSL2_injective (n : ℕ) (i : Fin n) : Function.Injective (blockSL2 K n i) :=
  blockSL_injective _

theorem blockSL3_injective (n : ℕ) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    Function.Injective (blockSL3 K n i h) :=
  blockSL_injective _

end Blocks

end CFSG.ClassicalInvolution.WeakCT
