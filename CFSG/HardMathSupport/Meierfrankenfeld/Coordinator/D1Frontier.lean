module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Assembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpLevi
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpCent
public import CFSG.HardMathSupport.Cooperstein.StructureLie.NeCaseAssembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.Final
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFive
public import CFSG.HardMathSupport.Meierfrankenfeld.E7Curtis.E7Family
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Coordinator

open CFSG.HardMathSupport.Cooperstein CFSG.HardMathSupport.Cooperstein.Coordinator

section Exceptional

theorem coopersteinNoFFExceptionalRestNoE8_of_e6Families (hE6 : CoopersteinNoIrrFFE6)
    (hTE6 : CoopersteinNoIrrFFTwistedE6) : CoopersteinNoFFExceptionalRestNoE8 :=
  coopersteinNoFFExceptionalRestNoE8_of_families hE6 hTE6 E7Curtis.coopersteinNoIrrFFE7

end Exceptional

section NonParabolic

theorem eightNineNonParabolic_of_lieInputRest (hrest : LieInput.LieInputRest) :
    StructureLie.EightNineNonParabolic :=
  have h := LieInput.lieInputStatement_of_rest LieInput.spLeviOb LieInput.spCentOb hrest
  (StructureLie.eightNineNonParabolic_of_bot
      (CFSG.AGLEmbedding.asc81bEightFive_of_factorization
          CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
      (StructureLie.eightNineBotCase_of_1311
          CFSG.HardMathSupport.Cooperstein.Coordinator.GF2Thm1311.gf2Thm1311Classical_holds) h.1 h.2)

end NonParabolic

end CFSG.HardMathSupport.Meierfrankenfeld.Coordinator
