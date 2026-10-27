module

public import CFSG.LargeExtraspecial.AS35DStmt

public section

namespace CFSG.LargeExtraspecial

open Subgroup

namespace AS62

variable {G : Type} [Group G] [Finite G]

structure W2Hyp (S : Setting G) : Prop where
  hw : S.width = 2
  hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z
  hO : ∀ t ∈ S.QG, orderOf t = 2 → S.ZInOTwo t
  hsimp : IsSimpleGroup S.zGen
  hC : centralizer (S.zGen : Set G) = ⊥

end AS62

end CFSG.LargeExtraspecial
