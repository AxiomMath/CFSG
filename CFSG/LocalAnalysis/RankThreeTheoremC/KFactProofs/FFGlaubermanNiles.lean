module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.AssemblyGraph
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbProved
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.SymOverFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Closed
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.FullAssemblyMilestoneFF
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.SharedFrontier
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBFinal
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthMinusCent
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs


open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry in
theorem ffModuleTheorem_holds
    : CFSG.HardMathSupport.Cooperstein.Coordinator.FFModuleTheorem :=
  CFSG.AGLEmbeddingD2.Tits.ffModuleTheorem_of_exceptionalRest
    (CFSG.HardMathSupport.Cooperstein.Coordinator.coopersteinNoFFExceptionalRest_of_noE8
      (CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.sharedD2Inputs_of_three
        (fun _ hf K _ _ _ hK σ hσ =>
          CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.twTypeBoundStmt_proved hf K hK σ hσ)
        CFSG.HardMathSupport.Cooperstein.StructureLie.orthMinusCentOb_proved
        (e0NonShortNotHYcStatement_of_caseI E0Sub.e0NonShortNotCaseIStatement_holds)).1)

theorem glaubermanNilesInput_holds
    :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNilesInput :=
  CFSG.AGLEmbeddingD2.GN.glaubermanNiles_of_print_cited
    (CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516_of_graphOrbit
      CFSG.AGLEmbeddingD2.Tits.GN516.kFactChevGraphOrbit_proved
      CFSG.AGLEmbeddingD2.Tits.GN516.agl81I516SymOver_holds)
    ffModuleTheorem_holds CFSG.AGLEmbeddingD2.McLaughlin.A7Six.gnAltSevenThreeRank_proved

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
