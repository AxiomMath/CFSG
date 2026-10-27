module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalDefs

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

@[expose] def permMatrix (σ : Equiv.Perm (Fin 3)) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => if j = σ i then 1 else 0

theorem permMatrix_mul_transpose (σ : Equiv.Perm (Fin 3)) :
    permMatrix σ * (permMatrix σ : Matrix (Fin 3) (Fin 3) K)ᵀ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMatrix, Matrix.of_apply]
  rw [show (∑ j, (if j = σ i then (1 : K) else 0) * (if j = σ k then (1 : K) else 0)) =
      ∑ j, (if j = σ i then (if j = σ k then (1 : K) else 0) else 0) by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = σ i <;> simp [h]]
  rw [Finset.sum_ite_eq', Matrix.one_apply]
  simp only [Finset.mem_univ, if_true]
  by_cases h : i = k <;> simp [h, Equiv.apply_eq_iff_eq]

theorem permMatrix_transpose_mul (σ : Equiv.Perm (Fin 3)) :
    (permMatrix σ : Matrix (Fin 3) (Fin 3) K)ᵀ * permMatrix σ = 1 := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, permMatrix, Matrix.of_apply]
  rw [show (∑ j, (if i = σ j then (1 : K) else 0) * (if k = σ j then (1 : K) else 0)) =
      ∑ j, (if i = σ j then (if k = σ j then (1 : K) else 0) else 0) by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = σ j <;> simp [h]]
  rw [Equiv.sum_comp σ (fun j => if i = j then (if k = j then (1 : K) else 0) else 0),
    Finset.sum_ite_eq, Matrix.one_apply]
  by_cases h : i = k <;> simp [h, eq_comm]

theorem permBlockMatrix_transpose_mul (σ : Equiv.Perm (Fin 3)) :
    (fromBlocks (permMatrix σ) 0 0 (permMatrix σ) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      fromBlocks (permMatrix σ) 0 0 (permMatrix σ) = fromBlocks 0 1 (-1) 0 := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]
  rw [permMatrix_transpose_mul]
  simp

@[expose] noncomputable def permBlockGL (σ : Equiv.Perm (Fin 3)) : GL (Fin 3 ⊕ Fin 3) K :=
  ⟨fromBlocks (permMatrix σ) 0 0 (permMatrix σ),
    fromBlocks (permMatrix σ)ᵀ 0 0 (permMatrix σ)ᵀ,
    by
      rw [fromBlocks_multiply]
      simp [permMatrix_mul_transpose]
    , by
      rw [fromBlocks_multiply]
      simp [permMatrix_transpose_mul]⟩

@[expose] noncomputable def permBlock (σ : Equiv.Perm (Fin 3)) : StatedSp 3 K :=
  ⟨permBlockGL σ, by
    rw [mem_statedSp_iff]
    exact permBlockMatrix_transpose_mul σ⟩

private theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin 3)) (d : Fin 3 → K) :
    permMatrix σ * diagonal d = diagonal (fun i => d (σ i)) * permMatrix σ := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, permMatrix, Matrix.of_apply]
  by_cases h : j = σ i
  · subst h
    simp
  · simp [h]

theorem permBlock_mul_block (σ : Equiv.Perm (Fin 3)) (g : Fin 3 → SL(2, K)) :
    permBlock σ * block g = block (fun i => g (σ i)) * permBlock σ := by
  apply Subtype.ext
  apply Units.ext
  change (fromBlocks (permMatrix σ) 0 0 (permMatrix σ) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *
      blockMatrix (fun i => (g i : Matrix (Fin 2) (Fin 2) K)) =
    blockMatrix (fun i => (g (σ i) : Matrix (Fin 2) (Fin 2) K)) *
      fromBlocks (permMatrix σ) 0 0 (permMatrix σ)
  unfold blockMatrix
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  congr 1
  · exact permMatrix_mul_diagonal σ (fun i => (g i : Matrix (Fin 2) (Fin 2) K) 0 0)
  · exact permMatrix_mul_diagonal σ (fun i => (g i : Matrix (Fin 2) (Fin 2) K) 0 1)
  · exact permMatrix_mul_diagonal σ (fun i => (g i : Matrix (Fin 2) (Fin 2) K) 1 0)
  · exact permMatrix_mul_diagonal σ (fun i => (g i : Matrix (Fin 2) (Fin 2) K) 1 1)

theorem conj_pow_val_of_inverter {G : Type*} [Group G] {s t : G} (hs : s ^ 3 = 1)
    (ht : t * s = s ^ 2 * t) (x : ZMod 3) : t * s ^ x.val * t⁻¹ = s ^ (-x).val := by
  have hconj : t * s * t⁻¹ = s ^ 2 := by
    rw [ht, mul_assoc, mul_inv_cancel, mul_one]
  have hpow : t * s ^ x.val * t⁻¹ = s ^ (2 * x.val) := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hconj, ← pow_mul]
  rw [hpow, pow_eq_pow_mod (2 * x.val) hs, pow_eq_pow_mod (-x).val hs]
  congr 1
  have hx : ∀ y : ZMod 3, (2 * y.val) % 3 = ((-y).val) % 3 := by decide
  exact hx x

theorem exists_realizer_perm {s : SL(2, K)} (hs : IsCubeRootBlock s) (σ : Equiv.Perm (Fin 3)) :
    ∃ n : StatedSp 3 K, ∀ v, n * c₀ hs v * n⁻¹ =
      c₀ hs (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
  refine ⟨permBlock σ, fun v => ?_⟩
  rw [c₀_apply hs, c₀_apply hs]
  have h := permBlock_mul_block σ (fun i => s ^ (Multiplicative.toAdd v i).val)
  calc permBlock σ * block (fun i => s ^ (Multiplicative.toAdd v i).val) * (permBlock σ)⁻¹
      = (block (fun i => s ^ (Multiplicative.toAdd v (σ i)).val) * permBlock σ) *
          (permBlock σ)⁻¹ := by rw [h]
    _ = block (fun i => s ^ (Multiplicative.toAdd v (σ i)).val) *
          (permBlock σ * (permBlock σ)⁻¹) := by rw [mul_assoc]
    _ = block (fun i => s ^ (Multiplicative.toAdd v (σ i)).val) := by
          rw [mul_inv_cancel, mul_one]

theorem exists_realizer_sign {s : SL(2, K)} (hs : IsCubeRootBlock s) (ε : Fin 3 → ZMod 3)
    (hε : ∀ i, ε i ≠ 0) :
    ∃ n : StatedSp 3 K, ∀ v, n * c₀ hs v * n⁻¹ =
      c₀ hs (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v i) := by
  obtain ⟨t, ht⟩ := hs.exists_inverter
  refine ⟨block (fun i => if ε i = 1 then (1 : SL(2, K)) else t), fun v => ?_⟩
  rw [c₀_apply hs, c₀_apply hs]
  simp only [toAdd_ofAdd]
  have hfun : (fun i : Fin 3 => if ε i = 1 then (1 : SL(2, K)) else t) *
        (fun i => s ^ (Multiplicative.toAdd v i).val) *
        (fun i : Fin 3 => if ε i = 1 then (1 : SL(2, K)) else t)⁻¹ =
      fun i => s ^ (ε i * Multiplicative.toAdd v i).val := by
    funext i
    by_cases h : ε i = 1
    · simp [h]
    · have hε' : ε i = -1 := by
        have : ∀ y : ZMod 3, y ≠ 0 → y ≠ 1 → y = -1 := by decide
        exact this (ε i) (hε i) h
      simp only [Pi.mul_apply, Pi.inv_apply, if_neg h]
      have hx : ε i * Multiplicative.toAdd v i = -(Multiplicative.toAdd v i) := by
        rw [hε']
        exact neg_one_mul (Multiplicative.toAdd v i)
      rw [hx]
      exact conj_pow_val_of_inverter hs.pow_three ht (Multiplicative.toAdd v i)
  rw [← map_inv, ← map_mul, ← map_mul, hfun]

theorem c₀_realizer {s : SL(2, K)} (hs : IsCubeRootBlock s) :
    ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) → ∃ n : StatedSp 3 K, ∀ v,
      n * c₀ hs v * n⁻¹ =
        c₀ hs (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
  intro σ ε hε
  obtain ⟨n₁, h₁⟩ := exists_realizer_perm hs σ
  obtain ⟨n₂, h₂⟩ := exists_realizer_sign hs ε hε
  refine ⟨n₂ * n₁, fun v => ?_⟩
  rw [show (n₂ * n₁)⁻¹ = n₁⁻¹ * n₂⁻¹ from _root_.mul_inv_rev n₂ n₁]
  calc n₂ * n₁ * c₀ hs v * (n₁⁻¹ * n₂⁻¹)
      = n₂ * (n₁ * c₀ hs v * n₁⁻¹) * n₂⁻¹ := by simp only [mul_assoc]
    _ = n₂ * c₀ hs (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) * n₂⁻¹ := by
          rw [h₁ v]
    _ = c₀ hs (Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd v (σ i)) := by
          exact h₂ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i))

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
