module


public import CFSG.LocalAnalysis.RankThreeUC.Section13.Context
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section21

variable {G : Type} [Group G] [Finite G]

@[expose] def oTwoF (M : Subgroup G) : Subgroup G :=
  ((CFSG.fittingSubgroup (Section13.Bar M)).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

end Section21

end CFSG.LocalAnalysis.RankThreeUC
