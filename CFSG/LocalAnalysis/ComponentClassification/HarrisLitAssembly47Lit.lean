module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAltCover
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Centralizer
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Involution
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2FieldCent
public import CFSG.RankThree.PartOne.SPOR.Final
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndGA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB34
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Asm
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2Fusion

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harris47_of_literature
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hT1 : Harris82Theorem1KProper) (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput)
    (h35 : Harris81Lemma35Step) (hCI : GSLit.ClassicalInvolutionInput)
    (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo) (hF : L4U4ThreeInvolutionFacts)
    (hC5 : L34CoverInvolutionFact) :
    Harris47Input :=
  have h34 : Harris81Lemma34Input := harris81Lemma34Input_of h311 h9
  have hGA : TBLit.GriessMultipliersOdd := TBLit.griessMultipliersOdd_holds
  have hC3 : L4U4InvolutionCentralizerFact := C3.l4u4InvolutionCentralizerFact
  have hQ81 : Harris47Q81Input := harris47Q81Input_of AutL2Facts.autPSL2FieldCentralizer
    AutL2Facts.cfAutPSL2Centralizer AutL2Facts.cfAutPSL2Sylow AutL2Facts.cfAutPSL2Fusion
    RankThree.PartOne.SPOR.schreierFor_catalog h219 hSD hGA hGC hT1 h34 hC3 hCI hP2 hT2 hF
  harris47_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
    AutL2Facts.cfAutPSL2Involution AutL2Facts.cfAutPSL2Sylow
    RankThree.PartOne.SPOR.schreierFor_catalog h219 hSD hGA hGC hT1 hCI h34 h35 hQ81 hC3 hC5
    alternatingCoverInvolutionFact_holds

end CFSG.ComponentClassification.HarrisLit
