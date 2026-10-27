module

public import CFSG.LinearAlgebra.CubeRootBlockTorus

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped MatrixGroups

theorem cubeRootBlock_transpose {F : Type} [Field F] [CharP F 2] :
    (cubeRootBlock F : Matrix (Fin 2) (Fin 2) F)ᵀ =
      (cubeRootBlock F : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeRootBlock, CharTwo.neg_eq]

theorem transpose_eq_of_commute_cubeRootBlock {F : Type} [Field F] [CharP F 2]
    {z : SpecialLinearGroup (Fin 2) F}
    (hz : Commute (z : Matrix (Fin 2) (Fin 2) F) (cubeRootBlock F : Matrix (Fin 2) (Fin 2) F)) :
    (z : Matrix (Fin 2) (Fin 2) F)ᵀ = (z : Matrix (Fin 2) (Fin 2) F) := by
  have h := hz.eq
  have h01 : (z : Matrix (Fin 2) (Fin 2) F) 0 1 = (z : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    have h0 := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, cubeRootBlock, CharTwo.neg_eq] using h0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01]

theorem exists_symmetric_sl2_orderOf_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hq3 : Nat.card F % 3 = 2) :
    ∃ g : SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F)ᵀ = (g : Matrix (Fin 2) (Fin 2) F) ∧ orderOf g = p := by
  have h3 : (3 : F) ≠ 0 := by
    intro h
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h1 : (3 : F) = (1 : F) := by
      rw [show (3 : F) = 1 + 2 by norm_num, h2, add_zero]
    rw [h1] at h
    exact one_ne_zero h
  rcases eq_or_ne p 3 with rfl | hp3
  · exact ⟨cubeRootBlock F, cubeRootBlock_transpose,
      (isCubeRootBlock_cubeRootBlock (K := F) h3).orderOf_eq_three⟩
  · obtain ⟨z, hz, hord⟩ := exists_commute_orderOf_eq_cubeRootBlock (K := F) h3 (by omega) hp
      (hp.five_le_of_ne_two_of_ne_three hp2 hp3) hpq
    exact ⟨z, transpose_eq_of_commute_cubeRootBlock hz, hord⟩

end CFSG.LinearAlgebra
