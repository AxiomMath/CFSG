module

public import CFSG.LargeExtraspecial.AS35YLSBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.Blueprint CFSG.RankThree.OrthogonalInvolutions

namespace S14

@[expose] def Asc512POmegaNatStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.Asc512Standing →
    InspNondeg _ S.EhatAsc →
    (LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaPlus S.width 2 1 ∨
      LieModel (S.LbarAsc ⧸ center S.LbarAsc) .POmegaMinus S.width 2 1) →
    S.LbarIrred_YL → False

end S14

end CFSG.LargeExtraspecial
