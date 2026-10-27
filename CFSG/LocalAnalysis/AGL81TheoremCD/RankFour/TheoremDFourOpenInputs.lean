module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.Section15FourInputs
public import CFSG.CGT.PushingUpLit.TwoKHolds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518Res
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Holds
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.Final
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenCentreFinal
import CFSG.LocalAnalysis.RankThreeUC.K518HMain
import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem agl81TheoremDFour_of_open_inputs
    (hK517_4b : K517_4b) (hK5192 : K5192P2)
    (hSix : GNSixAll)
    (h1211 : Section14.TwelveElevenGen) (h1217 : Section15.O1217Gen)
    (h1219 : Section15.O1219SigmaGen) (h1517 : Section15.O1517bGen)
    (h1521 : Section15.O1521Gen) (h1521b : Section15.O1521bGen)
    (h991 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen) (h89 : Section15.O89Gen)
    (h812 : Section15.O812sixGen) (hP812 : Section15.P812Gen) (h98 : Section15.O98Gen)
    (hGN : CFSG.LocalAnalysis.RankThreeUC.S15.S15GNInput) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour :=
  agl81TheoremDFour_of_cited_inputs
    CFSG.LocalAnalysis.RankThreeUC.S15.K4143_holds hK517_4b
    (CFSG.LocalAnalysis.RankThreeUC.S15.K518_of_residue
      CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen.kFactChevGenCentre_proved
      CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt_holds K518H.k518Y_holds) hK5192
    hSix h1211 h1217 h1219 h1517 h1521 h1521b h991 h89 h812 hP812 h98
    CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
    CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.agl81I59 hGN

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
