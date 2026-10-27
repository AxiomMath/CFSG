module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveNodes

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup

theorem blockSpecialLinear_union_eq_sup {n : ℕ} {K : Type*} [Field K]
    {I J : Finset (Fin n)} {c : Fin n} (hcI : c ∈ I) (hcJ : c ∈ J) :
    blockSpecialLinear (K := K) (I ∪ J) = blockSpecialLinear I ⊔ blockSpecialLinear J := by
  classical
  have hcross : ∀ {A B : Finset (Fin n)} {i j : Fin n}, c ∈ A → c ∈ B →
      i ∈ A → j ∈ B → (hij : i ≠ j) → ∀ t : K,
        SpecialLinearGroup.transvection hij t ∈ blockSpecialLinear A ⊔ blockSpecialLinear B := by
    intro A B i j hcA hcB hi hj hij t
    by_cases hic : i = c
    · subst i
      exact mem_sup_right (transvection_mem_blockSpecialLinear hij hcB hj t)
    by_cases hjc : j = c
    · subst j
      exact mem_sup_left (transvection_mem_blockSpecialLinear hij hi hcA t)
    have hA : blockSpecialLinear (K := K) (insert c {i}) ≤ blockSpecialLinear A :=
      blockSpecialLinear_mono (by simpa using Finset.insert_subset hcA (Finset.singleton_subset_iff.mpr hi))
    have hB : blockSpecialLinear (K := K) (insert c {j}) ≤ blockSpecialLinear B :=
      blockSpecialLinear_mono (by simpa using Finset.insert_subset hcB (Finset.singleton_subset_iff.mpr hj))
    exact ((OmegaPilot.blockSpecialLinear_pair_le_sup hij hic hjc).trans
      (sup_le_sup hA hB)) (transvection_mem_blockSpecialLinear hij (by simp) (by simp) t)
  apply le_antisymm ?_ (sup_le (blockSpecialLinear_mono Finset.subset_union_left)
    (blockSpecialLinear_mono Finset.subset_union_right))
  rw [blockSpecialLinear_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, t, hi, hj, rfl⟩
  rcases Finset.mem_union.mp hi with hi | hi <;> rcases Finset.mem_union.mp hj with hj | hj
  · exact mem_sup_left (transvection_mem_blockSpecialLinear hij hi hj t)
  · exact hcross hcI hcJ hi hj hij t
  · simpa [sup_comm] using hcross hcJ hcI hi hj hij t
  · exact mem_sup_right (transvection_mem_blockSpecialLinear hij hi hj t)

end CFSG.SeitzReduction.LinearPilot

end
