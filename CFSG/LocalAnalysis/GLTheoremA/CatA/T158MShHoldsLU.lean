module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormCat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShNormL3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShCompUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShLinTypeOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShUniTypeOne
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShIdentU6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShFixL2Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinUniBoundHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

section Comp


theorem t158CompLin_holds : T158CompLin :=
  t158CompLin_of T171Sh.linMarking_holds t158MISetup_holds
    (t158LinTypeOneW_of (T171Sh.linBlockInnDiag_of_stated T171Sh.linBlockInnDiagStated_holds))

theorem t158CompUni_holds : T158CompUni :=
  t158CompUni_of T171Sh.uniMarking_holds t158MISetup_holds
    (t158UniTypeOneW_of_block T171Sh.uniBlockInnDiag_holds)

end Comp

section Setup


theorem t158SetupLU_holds : T158SetupLU :=
  t158SetupLU_of (t158CompLU_of t158CompLin_holds t158CompUni_holds) t158ClaimLU_holds

end Setup

section Heads


theorem t158ShapeLieOn_A_holds
    : T158ShapeLieOn t158ShapeA :=
  t158ShapeLieOn_A
    (t158Norm_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds t158NormCat_holds
      t158NormL3_holds)
    t158SetupLU_holds T171Sh.linUniBound_holds

theorem t158ShapeLieOn_TwA_holds
    : T158ShapeLieOn t158ShapeTwA :=
  t158ShapeLieOn_TwA
    (t158Norm_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds t158NormCat_holds
      t158NormL3_holds)
    t158SetupLU_holds T171Sh.linUniBound_holds
    (t158IdentU6_of t158CompUni_holds) t158FixL2_holds

end Heads

end CFSG.LocalAnalysis.GLTheoremA.T158

end
