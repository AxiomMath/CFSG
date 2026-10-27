module

public import CFSG.Quasithin.Vol2.Ch11SecD551A

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem exists_gammaSet_zero_not_le_pCoreOf {V T H : Subgroup G}
    (hOT : pCoreOf 2 H ≤ T) (hW : ¬ H ≤ normalizer (E3.wClos V 0 T : Set G)) :
    ∃ A ∈ E3.gammaSet V 0 T, ¬ A ≤ pCoreOf 2 H := by
  by_contra hall
  push Not at hall
  apply hW
  have hle : E3.wClos V 0 T ≤ pCoreOf 2 H := E3.wClos_le_of_forall fun A hA => hall A hA
  rw [← CFSG.Quasithin.Vol2.Ch11.SecD.wClos_zero_eq_of_le hOT hle]
  have hHN : H ≤ normalizer (pCoreOf 2 H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).1
      (normal_pCoreOf_subgroupOf H)
  exact hHN.trans (E3.normalizer_le_normalizer_wClos _)

end CFSG.GroupTheory
