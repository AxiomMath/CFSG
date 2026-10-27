module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Singer
public import Mathlib.LinearAlgebra.Matrix.Transvection

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Matrix

@[expose] def gl4T : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 0, 1; 0, 1, 0, 0; 1, 0, 1, 1; 1, 1, 0, 1]

@[expose] def gl4N : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 0, 1, 0; 1, 1, 0, 0; 0, 1, 1, 1; 0, 1, 1, 0]

theorem singer_mul_pe : ∀ a b : Fin 3,
    singerMat ^ 5 * (singerMat ^ (5 * (a : ℕ)) * gl4T ^ (b : ℕ)) =
      singerMat ^ (5 * ((a + 1 : Fin 3) : ℕ)) * gl4T ^ (b : ℕ) := by decide

theorem gl4T_mul_pe : ∀ a b : Fin 3,
    gl4T * (singerMat ^ (5 * (a : ℕ)) * gl4T ^ (b : ℕ)) =
      singerMat ^ (5 * (a : ℕ)) * gl4T ^ ((b + 1 : Fin 3) : ℕ) := by decide

theorem singer_pow_five_mul_gl4N :
    singerMat ^ 5 * gl4N = gl4N * (singerMat ^ (5 * (1 : ℕ)) * gl4T ^ (2 : ℕ)) := by decide

theorem exists_pow_five_sub (w : Fin 4 → ZMod 2) :
    ∃ u : Fin 4 → ZMod 2, (singerMat ^ 5) *ᵥ u + u = w := by
  revert w
  decide

theorem gl4T_mulVec_injective : Function.Injective gl4T.mulVec := by
  have : ∀ u v : Fin 4 → ZMod 2, gl4T *ᵥ u = gl4T *ᵥ v → u = v := by decide
  exact fun u v h => this u v h

theorem gl4N_mulVec_injective : Function.Injective gl4N.mulVec := by
  have : ∀ u v : Fin 4 → ZMod 2, gl4N *ᵥ u = gl4N *ᵥ v → u = v := by decide
  exact fun u v h => this u v h

abbrev gl4Sub : Submonoid (Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  Submonoid.closure {singerMat, gl4N}

@[expose] def gl4Word : List Bool → Matrix (Fin 4) (Fin 4) (ZMod 2)
  | [] => 1
  | b :: w => (if b then gl4N else singerMat) * gl4Word w

theorem gl4Word_mem (w : List Bool) : gl4Word w ∈ gl4Sub := by
  induction w with
  | nil => exact gl4Sub.one_mem
  | cons b w ih =>
    refine gl4Sub.mul_mem ?_ ih
    cases b
    · exact Submonoid.subset_closure (by simp)
    · exact Submonoid.subset_closure (by simp)

@[expose] def gl4Words : List (List Bool) :=
  [[],
  [true, false, false, true, true, false, true, true, false, false, false, false, true, false,
    true],
  [false, true, false, true, false, true, true, false, true, false, false, true],
  [false, false, true, false, false, false, false, true, false, false],
  [false, false, false, true, false, false, false, false, true, false],
  [],
  [true, false, true, true, false, false, true, false, true, true, true, false, true, true,
    false, true],
  [false, false, false, false, false, false, false, false, true, false, false, true, true],
  [false, false, false, false, true, false, true, true, false, false, true, true, false, true,
    true],
  [true, true, false, false, true, true, false, false, true, true, false, true],
  [],
  [false, true, true, false, true, false, false, true, true, true, false, false, true, false,
    false, true],
  [true, false, true, true, true, false, false, true, true, false, true, false, false, true,
    false, false, false],
  [false, false, true, true, false, false, true, false, false, false, true, true, false, false,
    true, true, true],
  [true, false, true, false, false, true, false, true, true, false, true, false],
  []]

theorem gl4Words_spec : ∀ i j : Fin 4, i ≠ j →
    gl4Word (gl4Words.getD (4 * (i : ℕ) + (j : ℕ)) []) = transvection i j (1 : ZMod 2) := by
  decide

theorem transvection_mem_gl4Sub (i j : Fin 4) (hij : i ≠ j) (c : ZMod 2) :
    transvection i j c ∈ gl4Sub := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · rw [transvection_zero]
    exact gl4Sub.one_mem
  · rw [← gl4Words_spec i j hij]
    exact gl4Word_mem _

theorem mem_closure_singer_gl4N (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M.det ≠ 0) :
    M ∈ gl4Sub := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ gl4Sub) M hM
    (fun D hD => ?_) (fun t => transvection_mem_gl4Sub t.i t.j t.hij t.c)
    (fun A B _ _ hA hB => gl4Sub.mul_mem hA hB)
  have hD' : ∀ i, D i = 1 := by
    intro i
    have hi : D i ≠ 0 := by
      intro h0
      apply hD
      rw [det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    revert hi
    generalize D i = x
    revert x
    decide
  have hdiag : diagonal D = 1 := by
    have : D = fun _ => 1 := funext hD'
    rw [this]
    exact diagonal_one
  rw [hdiag]
  exact gl4Sub.one_mem

end CFSG.EvenSporadicStandard.ThStd
