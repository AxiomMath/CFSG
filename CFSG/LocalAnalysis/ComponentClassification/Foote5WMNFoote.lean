module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalanceWiring
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Thm
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLie
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreGriess
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndAsm
public import CFSG.LocalAnalysis.ComponentClassification.Foote5AscMain
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreExc3Out
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreONOut
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34Core
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreOddLieAut
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HallSDClose
public import CFSG.LocalAnalysis.ComponentClassification.CTUFooteConjugate

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG

theorem footeMaximalInput_of_conjugatePair
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hSol : Sol76T13.SolomonThm13Simple) (h2An : GSThmB.Solomon2AnInput)
    (hGH : UFrontier.GH74ModelsInput) (hodd : Foote5.OddLieOuterCoreInput)
    (hC : FooteConjugatePairExclusion) :
    FooteMaximalInput :=
  footeMaximalInput_of_known_inputs hCI hGA
    @Milestones.cl_lit_griess_schur_multipliers_central_covers
    Alternating.Multipliers.schurAlternatingMultiplierInput hSol
    (footeSolomonFamilyInput_of_conjugatePair hGA
      @Milestones.cl_lit_griess_schur_multipliers_central_covers
      Alternating.Multipliers.schurAlternatingMultiplierInput hC)
    foote_theorem_4_7 Foote5.aschbacherCentralCoreInput_holds h2An
    (Sol78.F514.footeRankTwoExclusion_of_open_inputs hCI hGA hGH Foote5.HallGen.goldschmidtCorB4)
    fun _ _ _ _ hna hK => footeCoreHypothesis_of_residual
      catalogAlmostSimpleUnbalancedOutcome_holds
      (footeCoreResidualInput_of_noHe (Foote5.footeCoreResidualInputNoHe_of_lie
          (Foote5.footeCoreResidualLieInput_of_parts (Foote5.footeCoreOddLieInput_of_outerCore hodd)
              Foote5.footeCoreL34Input_holds
              (Foote5.evenLieMultiplierOuterInput_of_exceptionalOuter
                  Foote5.evenLieExceptionalOuterInput_holds)) Foote5.oNanOuterCardLeTwo_holds)) hna hK

end CFSG.ComponentClassification.FooteLit
