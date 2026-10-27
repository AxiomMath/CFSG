module

public import CFSG.Open.StatedDefs
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix CFSG.Open

theorem charP_two_of_card_four (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  have hK' : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have hdvd : p ∣ 2 * 2 := by
    rw [show 2 * 2 = Fintype.card K by rw [hK'], hcard]
    exact dvd_pow_self p n.pos.ne'
  have hp2 : p = 2 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
  rw [hp2] at hchar
  exact hchar

theorem pow_four_eq_self (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4) (x : K) :
    x ^ 4 = x := by
  have := Fintype.ofFinite K
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, hK] at h
  exact h

@[expose] def sqHom (K : Type) [Field K] [CharP K 2] : K →+* K where
  toFun x := x ^ 2
  map_one' := one_pow 2
  map_mul' x y := mul_pow x y 2
  map_zero' := zero_pow two_ne_zero
  map_add' x y := add_pow_char x y 2

theorem sqHom_apply (K : Type) [Field K] [CharP K 2] (x : K) : sqHom K x = x ^ 2 := rfl

theorem sqHom_sqHom {K : Type} [Field K] [CharP K 2] (h4 : ∀ x : K, x ^ 4 = x) (x : K) :
    sqHom K (sqHom K x) = x := by
  rw [sqHom_apply, sqHom_apply, ← pow_mul]
  exact h4 x

theorem map_sqHom_map_sqHom {K : Type} [Field K] [CharP K 2] (h4 : ∀ x : K, x ^ 4 = x)
    (M : Matrix (Fin 3) (Fin 3) K) : (M.map (sqHom K)).map (sqHom K) = M := by
  ext i j
  simp [Matrix.map_apply, sqHom_sqHom h4]

theorem unitary_mul_mem {K : Type} [Field K] [CharP K 2] {M N : Matrix (Fin 3) (Fin 3) K}
    (hM : (M.map (sqHom K))ᵀ * M = 1) (hN : (N.map (sqHom K))ᵀ * N = 1) :
    ((M * N).map (sqHom K))ᵀ * (M * N) = 1 := by
  calc ((M * N).map (sqHom K))ᵀ * (M * N)
      = (N.map (sqHom K))ᵀ * ((M.map (sqHom K))ᵀ * M) * N := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hM, Matrix.mul_one, hN]

theorem unitary_inv_mem {K : Type} [Field K] [CharP K 2] (h4 : ∀ x : K, x ^ 4 = x)
    {M N : Matrix (Fin 3) (Fin 3) K} (hdet : M.det = 1) (hMu : (M.map (sqHom K))ᵀ * M = 1)
    (hMN : M * N = 1) : N.det = 1 ∧ (N.map (sqHom K))ᵀ * N = 1 := by
  have hNM : N = (M.map (sqHom K))ᵀ := by
    calc N = ((M.map (sqHom K))ᵀ * M) * N := by rw [hMu, one_mul]
      _ = (M.map (sqHom K))ᵀ * (M * N) := by rw [mul_assoc]
      _ = (M.map (sqHom K))ᵀ := by rw [hMN, mul_one]
  refine ⟨?_, ?_⟩
  · have h := congrArg Matrix.det hMN
    rw [Matrix.det_mul, hdet, one_mul, Matrix.det_one] at h
    exact h
  · have hT : (N.map (sqHom K))ᵀ = M := by
      rw [hNM, Matrix.transpose_map, map_sqHom_map_sqHom h4, Matrix.transpose_transpose]
    rw [hT]
    exact hMN

@[expose] def unitarySU32 (K : Type) [Field K] [CharP K 2] (h4 : ∀ x : K, x ^ 4 = x) :
    Subgroup (GL (Fin 3) K) where
  carrier := {A | (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
    ((A : Matrix (Fin 3) (Fin 3) K).map (sqHom K))ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1}
  mul_mem' := by
    intro A B hA hB
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.det_mul, hA.1, hB.1, one_mul]
    · rw [Units.val_mul]
      exact unitary_mul_mem hA.2 hB.2
  one_mem' := by
    refine ⟨?_, ?_⟩
    · simp
    · simp [Matrix.map_one]
  inv_mem' := by
    intro A hA
    exact unitary_inv_mem h4 hA.1 hA.2 (by simp)

theorem statedSU_three_two_eq (K : Type) [Field K] [CharP K 2] (h4 : ∀ x : K, x ^ 4 = x) :
    StatedSU 3 2 K = unitarySU32 K h4 := by
  apply le_antisymm
  · unfold StatedSU
    exact (Subgroup.closure_le _).2 fun B hB => hB
  · intro B hB
    exact Subgroup.subset_closure hB

theorem mem_StatedSU_three_two_iff (K : Type) [Field K] [Finite K] (hK : Nat.card K = 4)
    (A : GL (Fin 3) K) :
    A ∈ StatedSU 3 2 K ↔ (A : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) K).map (· ^ 2))ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1 := by
  have := charP_two_of_card_four K hK
  rw [statedSU_three_two_eq K (pow_four_eq_self K hK)]
  exact Iff.rfl

end CFSG.HardMathSupport.Solomon.Proving
