module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic
public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4NSAlg

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp

open QuadraticAlgebra CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
  CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

@[expose] def PhiFun (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.of fun a b => match a, b with
    | Sum.inl k, Sum.inl l => (N k l).re
    | Sum.inl k, Sum.inr l => -(N k l).im
    | Sum.inr k, Sum.inl l => (N k l).im
    | Sum.inr k, Sum.inr l => (N k l).re

theorem PhiFun_apply_ll (N : Matrix (Fin 2) (Fin 2) (QE F)) (k l : Fin 2) :
    PhiFun N (Sum.inl k) (Sum.inl l) = (N k l).re := rfl
theorem PhiFun_apply_lr (N : Matrix (Fin 2) (Fin 2) (QE F)) (k l : Fin 2) :
    PhiFun N (Sum.inl k) (Sum.inr l) = -(N k l).im := rfl
theorem PhiFun_apply_rl (N : Matrix (Fin 2) (Fin 2) (QE F)) (k l : Fin 2) :
    PhiFun N (Sum.inr k) (Sum.inl l) = (N k l).im := rfl
theorem PhiFun_apply_rr (N : Matrix (Fin 2) (Fin 2) (QE F)) (k l : Fin 2) :
    PhiFun N (Sum.inr k) (Sum.inr l) = (N k l).re := rfl

@[expose] def PhiS :
    Matrix (Fin 2) (Fin 2) (QE F) →+* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F where
  toFun := PhiFun
  map_one' := by
    ext a b
    rcases a with k | k <;> rcases b with l | l <;> fin_cases k <;> fin_cases l <;>
      simp [PhiFun, Matrix.one_apply]
  map_zero' := by
    ext a b
    rcases a with k | k <;> rcases b with l | l <;> simp [PhiFun]
  map_add' N N' := by
    ext a b
    rcases a with k | k <;> rcases b with l | l <;> simp [PhiFun] <;> ring
  map_mul' N N' := by
    ext a b
    rcases a with k | k <;> rcases b with l | l <;>
      simp [PhiFun, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

theorem PhiS_apply (N : Matrix (Fin 2) (Fin 2) (QE F)) : PhiS N = PhiFun N := rfl

theorem PhiS_injective : Function.Injective (PhiS : Matrix (Fin 2) (Fin 2) (QE F) →+* _) := by
  intro N N' h
  refine Matrix.ext fun k l => ?_
  have h1 := congrFun (congrFun h (Sum.inl k)) (Sum.inl l)
  have h2 := congrFun (congrFun h (Sum.inr k)) (Sum.inl l)
  simp only [PhiS_apply, PhiFun_apply_ll, PhiFun_apply_rl] at h1 h2
  exact QuadraticAlgebra.ext h1 h2

theorem PhiS_transpose (N : Matrix (Fin 2) (Fin 2) (QE F)) : (PhiS N)ᵀ = PhiS Nᴴ := by
  ext a b
  rcases a with k | k <;> rcases b with l | l <;>
    simp [PhiS_apply, PhiFun, Matrix.transpose_apply, Matrix.conjTranspose_apply]

theorem gram_mul_PhiS (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    gram F 2 * PhiS N = PhiS N * gram F 2 := by
  ext a b
  rcases a with k | k <;> rcases b with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [gram, Matrix.mul_apply, Fintype.sum_sum_type, PhiS_apply, PhiFun,
      Matrix.fromBlocks, Matrix.one_apply]

theorem eq_one_of_gram_mul_eq {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : gram F 2 * M = gram F 2) : M = 1 := by
  have := congrArg (fun X => gram F 2 * X) h
  simp only [← Matrix.mul_assoc, gram_mul_gram, Matrix.neg_mul, Matrix.one_mul, neg_inj] at this
  exact this

theorem PhiS_symplectic_iff (N : Matrix (Fin 2) (Fin 2) (QE F)) :
    (PhiS N)ᵀ * gram F 2 * PhiS N = gram F 2 ↔ Nᴴ * N = 1 := by
  have e : (PhiS N)ᵀ * gram F 2 * PhiS N = gram F 2 * PhiS (Nᴴ * N) := by
    rw [PhiS_transpose, ← gram_mul_PhiS, Matrix.mul_assoc, ← map_mul]
  rw [e]
  constructor
  · intro h
    exact PhiS_injective (by rw [map_one]; exact eq_one_of_gram_mul_eq h)
  · intro h
    rw [h, map_one, Matrix.mul_one]

theorem exists_PhiS_of_comm {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (h : M * gram F 2 = gram F 2 * M) : ∃ N, PhiS N = M := by
  refine ⟨Matrix.of fun k l => (⟨M (Sum.inl k) (Sum.inl l), -M (Sum.inl k) (Sum.inr l)⟩ : QE F),
    ?_⟩
  have e1 : ∀ k l : Fin 2, M (Sum.inr k) (Sum.inl l) = -M (Sum.inl k) (Sum.inr l) := fun k l => by
    have := congrFun (congrFun h (Sum.inl k)) (Sum.inl l)
    simpa [gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
      using this.symm
  have e2 : ∀ k l : Fin 2, M (Sum.inr k) (Sum.inr l) = M (Sum.inl k) (Sum.inl l) := fun k l => by
    have := congrFun (congrFun h (Sum.inl k)) (Sum.inr l)
    simpa [gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
      using this.symm
  ext a b
  rcases a with k | k <;> rcases b with l | l <;>
    simp [PhiS_apply, PhiFun, e1, e2]


end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerSp
