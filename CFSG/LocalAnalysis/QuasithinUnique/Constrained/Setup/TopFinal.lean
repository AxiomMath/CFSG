module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopPieces
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftBlockTransfer

public section

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Lift

theorem minParabolicBlocks_final
    (hJ4 : X1.SporadicExclusion .J4) : MinParabolicBlocks :=
  minParabolicBlocks_of_pieces blockTransferProp hJ4

end CFSG.QuasithinUnique.Setup.Top
