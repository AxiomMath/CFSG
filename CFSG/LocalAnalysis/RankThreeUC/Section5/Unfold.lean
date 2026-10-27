module

public import CFSG.LocalAnalysis.RankThreeUC.Section21.ResidualComponentInversion

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

theorem oTwoF_eq {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Section21.oTwoF M =
      ((CFSG.fittingSubgroup (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype := by
  unfold Section21.oTwoF
  rfl

end Section5
end CFSG.LocalAnalysis.RankThreeUC
