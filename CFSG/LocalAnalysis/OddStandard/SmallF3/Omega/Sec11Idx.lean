module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_le_normalizer_of_relIndex_two {S T : Subgroup G} (hST : S ≤ T)
    (hidx : S.relIndex T = 2) : T ≤ normalizer (S : Set G) := by
  have hN : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hST).mp hN

end CFSG.OddStandard.SmallF3.Omega
