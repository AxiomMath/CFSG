module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellShort

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {X T P K : Subgroup G} (S : Setting X T P K)

include S

theorem blockU_le_T : blockU K ≤ T := by
  have hTP : IsSylowTwoOf T P := CFSG.Quasithin.C1GN.isSylowTwoOf_of_le S.sylow S.TP S.PX
  refine (C1.blockU_le_blockQ S.short).trans ?_
  refine (Setup.Campbell.pCoreOf_le_of_isSubnormal 2 S.KP S.block.2.2).trans ?_
  exact pCoreOf_le_of_isSylowTwoOf hTP

end Setting

end L246C127

end CFSG.QuasithinUnique
