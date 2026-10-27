module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415WiringLit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB413Lit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB414Lit
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralFinal
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitTheoremB
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralFritzL2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Sec6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMain
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abACase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBMain
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cMain
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harrislit_of_inputs_main415
    (hGH : UFrontier.GH74ModelsInput) (hGHC : GHarris.GorensteinHaradaThmCInput)
    (hI48 : CFSG.Quasithin.HSType.StatementI48)
    (hCI : GSLit.ClassicalInvolutionInput)
    (hT1 : Harris82Theorem1KProper) (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput)
    (h35 : Harris81Lemma35Step) (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo)
    (hF : L4U4ThreeInvolutionFacts)
    (h36 : Harris81Lemma36NonsimpleInput) (hin : Harris36SimpleInput) : GSLit.HarrisInput :=
  harrislit_of_inputs_46e FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds hGH
      (HSFLit.hsflit_of_steps hGH OddStandard.Harada75.haradaInput_holds
          (GHarris.gorensteinHarrisInput_of hGHC hI48) HSFLit.ghPresentationBound HSFLit.ghRelInHS
          HSFLit.Sec8.fritz812dNotSylow HSDihedral.FritzL2.fritzL2Lemma36Final
          HSDihedral.FritzL2.fritzL2Lemma378 HSFLit.fritzL2KDFacts HSFLit.fritzKDSection4
          HSFLit.fritzKDSection6 HSFLit.fritzKDSection7
          (HSFLit.KD8ab.fritzKDSection8ab_of_cases HSFLit.KD8ab.caseA HSFLit.KD8abB.caseB)
          HSFLit.KD8c.fritzKDSection8c)
      HSDihedral.harrisSolomonDihedralInput AutL2Facts.cfAutPSL2Sylow
      AutL2Facts.cfAutPSL2Centralizer AutL2Facts.cfAutPSL2Fusion AutL2Facts.autPSL2FieldCentralizer
      AutL2Facts.cfAutPSL2Involution AutL2Facts.autPSL2FieldClass
      RankThree.PartOne.SPOR.schreierFor_catalog
      (harris413Input46e_of_literature hCI hT1 h311 h9 h35 hP2 hT2 hF hin)
      (harris414Input46e_of_literature hCI hT1 h311 h9 h35 hP2 hT2 hF h36)
      (harris415Input46e_of_literature RankThree.PartOne.SPOR.schreierFor_catalog
          harris82Lemma219Input_holds (harris46Semidihedral_of_classical hCI)
          (harris46Quaternion_of_classical RankThree.PartOne.SPOR.schreierFor_catalog
              AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hCI) hT1 h311 h9 h35 hCI
          hP2 hT2 hF h36 hin)

end CFSG.ComponentClassification.HarrisLit
