module

public import CFSG.LieType.BorelTits.Basic

public section


namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddKernelSylowNormal


open scoped Pointwise


variable {G : Type} [Group G]


instance pCoreOf_subgroupOf_normal (H : Subgroup G) :
    ((CFSG.Open.pCoreOf 2 H).subgroupOf H).Normal := by
  unfold CFSG.Open.pCoreOf
  show (Subgroup.comap H.subtype (Subgroup.map H.subtype _)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact CFSG.LieType.BorelTits.pCore_normal 2


end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddKernelSylowNormal
