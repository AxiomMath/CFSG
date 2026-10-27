module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Sstar (P T B : Subgroup G) : Subgroup (MulAut ↥P) :=
  ((twoCoreCommutator T B).subgroupOf (Subgroup.normalizer (P : Set G))).map (Subgroup.normalizerMonoidHom P)

@[expose] def Bstar (P B : Subgroup G) : Subgroup (MulAut ↥P) :=
  (B.subgroupOf (Subgroup.normalizer (P : Set G))).map (Subgroup.normalizerMonoidHom P)

end Section5

end CFSG.LocalAnalysis.RankThreeUC
