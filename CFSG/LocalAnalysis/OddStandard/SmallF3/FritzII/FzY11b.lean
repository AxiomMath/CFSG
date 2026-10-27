module

public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQ
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AS81

variable {G : Type} [Group G]

abbrev FzCbar (z : G) : Type := ↥(centralizer ({z} : Set G)) ⧸ zpowers (zC z)

abbrev fzBar (z : G) (A : Subgroup G) : Subgroup (FzCbar z) :=
  (A.subgroupOf (centralizer ({z} : Set G))).map (QuotientGroup.mk' (zpowers (zC z)))

end CFSG.OddStandard.SmallF3.FritzII
