module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11I102
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11U62Rank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

theorem i102InnAt_holds
    (G : Type) [Group G] [Finite G] : I102InnAt G :=
  i102InnAt_of_u6 (fun S _ hS F hF => U62RankSound.card_le_81_of_catalogIs hS hF) G

end CFSG.LocalAnalysis.GLTheoremA.CatB
