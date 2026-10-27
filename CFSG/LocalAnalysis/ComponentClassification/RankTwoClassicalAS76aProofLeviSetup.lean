module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

section Std

variable {K : Type} [Field K] {k : ℕ}

@[expose] noncomputable def stdE (hk : 2 ≤ k) : Matrix (Fin (2 + k)) (Fin (2 + k)) K :=
  blk 0 (single ⟨0, by omega⟩ ⟨1, by omega⟩ 1)

theorem blk_apply_inr (X : Matrix (Fin 2) (Fin 2) K) (S : Matrix (Fin k) (Fin k) K)
    (i j : Fin k) :
    blk X S (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = S i j := by
  rw [blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, fromBlocks_apply₂₂]

theorem stdE_eq_single (hk : 2 ≤ k) :
    stdE (K := K) hk = single (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
      (finSumFinEquiv (Sum.inr ⟨1, by omega⟩)) 1 := by
  ext x y
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective y
  rw [stdE, blk, coe_reindexAlgEquiv, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, single_apply]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rcases x with x | x <;> rcases y with y | y
  · simp
  · simp
  · simp
  · rw [fromBlocks_apply₂₂, single_apply]
    simp

theorem stdE_ne_zero (hk : 2 ≤ k) : stdE (K := K) hk ≠ 0 := by
  intro h
  have := congrFun (congrFun h (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)))
    (finSumFinEquiv (Sum.inr ⟨1, by omega⟩))
  rw [stdE, blk_apply_inr] at this
  simp at this

theorem stdE_mul_self (hk : 2 ≤ k) : stdE (K := K) hk * stdE hk = 0 := by
  have h : single (⟨0, by omega⟩ : Fin k) (⟨1, by omega⟩ : Fin k) (1 : K) *
      single (⟨0, by omega⟩ : Fin k) (⟨1, by omega⟩ : Fin k) (1 : K) = 0 := by
    simp [Fin.ext_iff]
  rw [stdE, blk_mul, Matrix.zero_mul, h, blk, fromBlocks_zero, map_zero]

theorem rank_stdE (hk : 2 ≤ k) : (stdE (K := K) hk).rank = 1 := by
  have h1 : (stdE (K := K) hk).rank ≤ 1 := by
    rw [stdE_eq_single, single_eq_single_vecMulVec_single]
    exact rank_vecMulVec_le _ _
  have h2 : (stdE (K := K) hk).rank ≠ 0 := fun h => stdE_ne_zero hk (eq_zero_of_rank_eq_zero h)
  omega

theorem one_add_smul_stdE (hk : 2 ≤ k) (a : K) :
    1 + a • stdE (K := K) hk = blk 1 (1 + single ⟨0, by omega⟩ ⟨1, by omega⟩ a) := by
  rw [stdE, blk_smul, smul_zero, ← blk_one, blk_add, add_zero, smul_single, smul_eq_mul, mul_one]

end Std

end CFSG.ComponentClassification.RankTwoClassical
