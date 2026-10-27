module

public import CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocalBlockRank
import CFSG.LinearAlgebra.CubeRootBlockTorus

public section

namespace CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.LinearAlgebra
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem two_le_pRank_centralizer_range_c₀ [Finite K] (h3 : (3 : K) ≠ 0) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : p ∣ if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) :
    2 ≤ CFSG.Open.pRank p (Subgroup.centralizer
      (((c₀ (isCubeRootBlock_cubeRootBlockStd h3)).range : Subgroup (StatedSp 3 K)) :
        Set (StatedSp 3 K))) := by
  obtain ⟨z, hzc, hz⟩ := exists_commute_orderOf_eq_cubeRootBlockStd h3 hp h5 hpq
  have hmem : ∀ i : Fin 3, block (Pi.mulSingle i z) ∈ Subgroup.centralizer
      (((c₀ (isCubeRootBlock_cubeRootBlockStd h3)).range : Subgroup (StatedSp 3 K)) :
        Set (StatedSp 3 K)) := by
    intro i
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, rfl⟩
    exact (commute_block_mulSingle_c₀_of_commute (isCubeRootBlock_cubeRootBlockStd h3)
      hzc i v).symm.eq
  exact two_le_pRank_of_block_mulSingle hp hz (i := 0) (j := 1) (by decide) (hmem 0) (hmem 1)

end CFSG.ClassicalGroups.Symplectic.Sp6ThreeLocal
