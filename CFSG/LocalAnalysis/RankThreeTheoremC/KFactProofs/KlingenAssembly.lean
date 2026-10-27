module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSp4Local
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62KlingenLocal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentLieMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentA9
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenIdentSporMain
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieCharPAll
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.P1ThreeLieOffCharHolds
public import CFSG.LocalAnalysis.AGLEmbedding.POneThreeAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeSporMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

theorem kFactKlingenLocal_holds :
    KFactKlingenLocal where
  outer := kFactKlingenLocal_outer
  inSitu := kFactKlingenLocal_inSitu_of_sp62 fun p _ hp3 d hd =>
    kFactKlingenLocal_inSitu_sp62 p (by omega) d ⟨hp3, hd⟩

theorem kFactKlingenThreeLocal_holds :
    KFactKlingenThreeLocal :=
  kFactKlingenThreeLocal_of_sp62 kFactKlingenThreeLocal_sp62

theorem kFactKlingenIdent_holds :
    KFactKlingenIdent :=
  kFactKlingenIdent_of_rows
    (CFSG.AGLEmbedding.kFactP1ThreeLie_of_charP_offChar CFSG.AGLEmbedding.p1ThreeLieOffChar_holds)
    CFSG.AGLEmbedding.kFactP1ThreeAlt CFSG.AGLEmbedding.kFactP1ThreeSpor klingenIdentLie_holds
    klingenIdentAlt_holds klingenIdentSpor_holds

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
