module

public import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem pCoreOf_eq_of_le_of_normal (p : ℕ) {P N : Subgroup G} (hNP : N ≤ P)
    (hN : (N.subgroupOf P).Normal) (hO : CFSG.Open.pCoreOf p P ≤ N) :
    CFSG.Open.pCoreOf p N = CFSG.Open.pCoreOf p P := by
  refine le_antisymm ?_ ?_
  · exact pCoreOf_le_pCoreOf_of_le_normalizer p hNP
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNP).1 hN)
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := p) hO
      (hNP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p P))
      ((CFSG.pCore_isPGroup (p := p) (G := ↥P)).map P.subtype)

end CFSG.GroupTheory
