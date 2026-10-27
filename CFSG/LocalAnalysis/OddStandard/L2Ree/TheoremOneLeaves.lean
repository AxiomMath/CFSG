module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1OfCI
public import CFSG.Quasithin.Recognition.HSType17m
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRE1All
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Final
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Main
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36HS2BMain
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36U4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC311b
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCatalogueU
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC9c
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofA6All
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitTheoremB
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDFacts
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralFritzL2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46Sec6
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8GapMain
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisCore
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisE16e
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abACase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBMain
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cMain
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralFinal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB413Lit
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Asm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinFamily
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinORow
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinExcRT
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporAll
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXHS
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXHe
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXON
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXSuz
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB414Lit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415WiringLit

public section

namespace CFSG.OddStandard.L2Ree

open CFSG CFSG.ComponentClassification CFSG.Assembly CFSG.Blueprint

section Certified

open _root_.Certificates


theorem theoremOne_of_leaves
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput) :
    HarrisLit.TheoremOne := by
  have hT1 := HarrisLit.T1.harris82Theorem1KProper_of_ci hCI
  have hGA : TBLit.GriessMultipliersAllModels := TBLit.griessMultipliersAllModels_holds
  have hGLS : CatLeaf.GLS3OddLieAutComponentsInput := GrSLit.gls3OddLieAutComponentsInput_holds
  have hI48 : CFSG.Quasithin.HSType.StatementI48 := CFSG.Quasithin.HSType.statementI48_holds
  have hCO : HarrisLit.L33.E1.ChevOddInnerInput := HarrisLit.L33.E1.chevOddInnerInput_holds
  have hP2 : HarrisLit.Harris81Lemma33Simple :=
    HarrisLit.L33.harris81Lemma33Simple_of_open hGA hCO
  have hONOL : SolMax.ONOuterLocalInput := SolMax.ONOut.onOuterLocalInput_holds
  have hONO : SolMax.ONOuterComponentsInput := SolMax.onOuterComponentsInput_of_local hONOL
  have hES : HarrisLit.Harris81Lemma35IdentEvenSporFact :=
    HarrisLit.harris81Lemma35IdentEvenSporFact_of_spor hGLS hGA
      SolMax.H35.harris81Lemma35IdentSporFact_holds
  have hID : HarrisLit.Harris81Lemma35IdentFact :=
    HarrisLit.harris81Lemma35IdentFact_of_nonAlt hCI
      (HarrisLit.harris81Lemma35IdentNonAltFact_of_resid
        Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
        EvenSporadicStandard.centralTwoBound
        (HarrisLit.harris81Lemma35IdentResidFact_of_cover hGLS hGA
          (HarrisLit.harris81Lemma35IdentCoverFact_of_four
            (HarrisLit.harris81Lemma35IdentFourCoverFact_of_evenSpor hGA hES))))
  have hT2 : HarrisLit.Harris82Theorem2SLTwo :=
    HarrisLit.harris82Theorem2SLTwo_of_theorem1 hT1 hGA hID
  have hT3 : HarrisLit.Harris82Theorem3SLTwo :=
    HarrisLit.harris82Theorem3SLTwo_of_theorem1 hT1 hGA hID hCI
  have h36B : HarrisLit.N36.EvenLieOuterCoverFact :=
    GrSLit.L34Facts.EvenCover.evenLieOuterCoverFact_of_multipliers hGA
  have h36 : HarrisLit.Harris81Lemma36NonsimpleInput :=
    HarrisLit.N36.statement_holds
      Sporadic.Recognition.HeMultiplier.heldTrivialMultiplier_of_certificate
      EvenSporadicStandard.centralTwoBound
      HarrisLit.N36.HS2B.twoHSTwoBFact_holds hONO hGLS
      HarrisLit.N36.EvenOddCore.evenLieInvolutionOddCoreFact_holds h36B
      HarrisLit.N36.OddChar.pslTwoOddCharacteristicFact_holds
      HarrisLit.N36.l4U4PartialCoverFact_holds hGA
  have h311 := HarrisLit.C311.harris311PSL2_of FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
    RankThree.PartOne.SPOR.schreierFor_catalog
  have h9 := HarrisLit.C9.harris34Nine_of FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
    RankThree.PartOne.SPOR.schreierFor_catalog CatLeafProof.oddLieA6ComponentCentre_holds
  have h35 := HarrisLit.L35.statement_holds_slTwo hT1 hT3 hID
  exact HarrisLit.theoremOne_of_inputs hGH
    (HSFLit.hsflit_of_steps hGH OddStandard.Harada75.haradaInput_holds
        (GHarris.gorensteinHarrisInput_of GHarris.gorensteinHaradaThmCInput_holds hI48)
        HSFLit.ghPresentationBound HSFLit.ghRelInHS HSFLit.Sec8.fritz812dNotSylow
        HSDihedral.FritzL2.fritzL2Lemma36Final HSDihedral.FritzL2.fritzL2Lemma378
        HSFLit.fritzL2KDFacts HSFLit.fritzKDSection4 HSFLit.fritzKDSection6 HSFLit.fritzKDSection7
        (HSFLit.KD8ab.fritzKDSection8ab_of_cases HSFLit.KD8ab.caseA HSFLit.KD8abB.caseB)
        HSFLit.KD8c.fritzKDSection8c)
    HSDihedral.harrisSolomonDihedralInput
    (HarrisLit.sectionFour_of_after42 AutL2Facts.cfAutPSL2Sylow
      (HarrisLit.sectionFourAfter42_of_after411 AutL2Facts.cfAutPSL2Fusion
        AutL2Facts.cfAutPSL2Centralizer
        (HarrisLit.sectionFourAfter411_of_46e AutL2Facts.autPSL2FieldCentralizer
          AutL2Facts.cfAutPSL2Centralizer AutL2Facts.cfAutPSL2Fusion
          AutL2Facts.cfAutPSL2Involution AutL2Facts.autPSL2FieldClass
          RankThree.PartOne.SPOR.schreierFor_catalog
          (HarrisLit.harris413Input46e_of_literature hCI hT1 h311 h9 h35 hP2 hT2
            HarrisLit.P1.l4U4ThreeInvolutionFacts (HarrisLit.Hin.harris36SimpleInput_of_rows
                HarrisLit.Hin.hinFor_alt HarrisLit.Hin.hinFor_classicalRep
                HarrisLit.Hin.hinFor_exceptionalRep
                (HarrisLit.Hin.hinFor_sporadicRep_of_rows HarrisLit.Hin.hinFor_spor_HS
                    HarrisLit.Hin.hinFor_spor_He HarrisLit.Hin.hinFor_spor_ON
                    HarrisLit.Hin.hinFor_spor_Suz)))
          (HarrisLit.harris414Input46e_of_literature hCI hT1 h311 h9 h35 hP2 hT2
            HarrisLit.P1.l4U4ThreeInvolutionFacts h36)
          (HarrisLit.harris415Input46e_of_literature RankThree.PartOne.SPOR.schreierFor_catalog
            HarrisLit.harris82Lemma219Input_holds (HarrisLit.harris46Semidihedral_of_classical hCI)
            (HarrisLit.harris46Quaternion_of_classical RankThree.PartOne.SPOR.schreierFor_catalog
              AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hCI)
            hT1 h311 h9 h35 hCI hP2 hT2 HarrisLit.P1.l4U4ThreeInvolutionFacts h36
            (HarrisLit.Hin.harris36SimpleInput_of_rows HarrisLit.Hin.hinFor_alt
                HarrisLit.Hin.hinFor_classicalRep HarrisLit.Hin.hinFor_exceptionalRep
                (HarrisLit.Hin.hinFor_sporadicRep_of_rows HarrisLit.Hin.hinFor_spor_HS
                    HarrisLit.Hin.hinFor_spor_He HarrisLit.Hin.hinFor_spor_ON
                    HarrisLit.Hin.hinFor_spor_Suz))))))

end Certified

end CFSG.OddStandard.L2Ree
