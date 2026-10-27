module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Rot

public section

namespace CFSG.SectionRank.ClassicalEven

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

theorem spForm_mulVec_inl (k : Fin n) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      Pi.single (Sum.inl k) 1 = -Pi.single (Sum.inr k) 1 := by
  rw [mulVec_single_one]
  ext (a | a) <;> simp [one_apply, Pi.single_apply]

theorem spForm_mulVec_inr (k : Fin n) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *ᵥ
      Pi.single (Sum.inr k) 1 = Pi.single (Sum.inl k) 1 := by
  rw [mulVec_single_one]
  ext (a | a) <;> simp [one_apply, Pi.single_apply]

theorem rotMatrix_inl_inr_symplectic (k : Fin n) :
    (rotMatrix (K := K) (Sum.inl k) (Sum.inr k))ᵀ * fromBlocks 0 1 (-1) 0 *
      rotMatrix (Sum.inl k) (Sum.inr k) = fromBlocks 0 1 (-1) 0 := by
  have hk : (Sum.inl k : Fin n ⊕ Fin n) ≠ Sum.inr k := Sum.inl_ne_inr
  refine ext_of_mulVec_single fun b => ?_
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  rcases b with c | c
  · by_cases hc : c = k
    · rw [hc, rotMatrix_mulVec_left, spForm_mulVec_inr, rotMatrix_transpose_mulVec_left hk,
        spForm_mulVec_inl]
    · have h1 : (Sum.inl c : Fin n ⊕ Fin n) ≠ Sum.inl k := by simpa using hc
      have h2 : (Sum.inr c : Fin n ⊕ Fin n) ≠ Sum.inr k := by simpa using hc
      rw [rotMatrix_mulVec_of_ne h1 Sum.inl_ne_inr, spForm_mulVec_inl, mulVec_neg,
        rotMatrix_transpose_mulVec_of_ne Sum.inr_ne_inl h2]
  · by_cases hc : c = k
    · rw [hc]
      simp only [rotMatrix_mulVec_right hk, mulVec_sub, mulVec_neg, spForm_mulVec_inl,
        spForm_mulVec_inr, rotMatrix_transpose_mulVec_left hk, rotMatrix_transpose_mulVec_right hk]
      abel
    · have h1 : (Sum.inl c : Fin n ⊕ Fin n) ≠ Sum.inl k := by simpa using hc
      have h2 : (Sum.inr c : Fin n ⊕ Fin n) ≠ Sum.inr k := by simpa using hc
      rw [rotMatrix_mulVec_of_ne Sum.inr_ne_inl h2, spForm_mulVec_inr,
        rotMatrix_transpose_mulVec_of_ne h1 Sum.inl_ne_inr]

theorem psl_three_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 6 ≤ n) : 3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSL n K))) :=
  three_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).comp finSumFinEquiv.injective)
    fun _ => Subgroup.subset_closure (det_rotMatrix _ _)

theorem psp_three_le_pRank_three {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) : 3 ≤ pRank 3 (⊤ : Subgroup (StatedProj (StatedSp n K))) :=
  three_le_pRank_three_of_rotGL ((Fin.castLE_injective hn).sumMap (Fin.castLE_injective hn))
    fun _ => Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _)

end CFSG.SectionRank.ClassicalEven
