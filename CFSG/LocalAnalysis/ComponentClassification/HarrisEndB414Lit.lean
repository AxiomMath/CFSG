module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB414J2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB414L34
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL34Facts
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1Simple
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma36Derive
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly47Lit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSD46B

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harris414Input46e_of_literature
    (hCI : GSLit.ClassicalInvolutionInput)
    (hT1 : Harris82Theorem1KProper) (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput)
    (h35 : Harris81Lemma35Step) (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo)
    (hF : L4U4ThreeInvolutionFacts)
    (h36 : Harris81Lemma36NonsimpleInput) : Harris414Input46e :=
  have h34 : Harris81Lemma34Input := harris81Lemma34Input_of h311 h9
  have hGA : TBLit.GriessMultipliersOdd := TBLit.griessMultipliersOdd_holds
  have hGC : TBLit.GriessMultipliersCentralCovers :=
    @CFSG.Milestones.cl_lit_griess_schur_multipliers_central_covers
  have hSch := RankThree.PartOne.SPOR.schreierFor_catalog
  have hSD : Harris46SemidihedralInput := harris46Semidihedral_of_classical hCI
  have hQI : Harris46QuaternionInput := harris46Quaternion_of_classical hSch
    AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hCI
  have h412 := harris412_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
      (harris46c_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch
          harris82Lemma219Input_holds hSD)
      (harris46d_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch
          harris82Lemma219Input_holds hSD hGA hGC hCI h34)
      (harris46eOdd_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch
          harris82Lemma219Input_holds hSD hGA hGC hCI h34)
      (harris46g_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch hQI)
  have h47 := harris47_of_literature harris82Lemma219Input_holds hSD hGC hT1 h311 h9 h35 hCI hP2
    hT2 hF GrSLit.L34Facts.l34CoverInvolutionFact
  harris414_of_cases (harris36NonsimpleInput_of_printed h36)
    (harris82TheoremOneKProper_of hGA hT1) h412 h47 (EndB.harris414_J2
        AutL2Facts.autPSL2FieldCentralizer
        AutL2Facts.cfAutPSL2Centralizer AutL2Facts.cfAutPSL2Involution AutL2Facts.cfAutPSL2Fusion)
            (EndB.harris414_L34 AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
                AutL2Facts.cfAutPSL2Involution AutL2Facts.cfAutPSL2Fusion
                GrSLit.L34Facts.l34UnitaryCentralizerFact EndB.l34FieldSylowFusionFact
                EndB.l34CyclicFourCenterFact)

end CFSG.ComponentClassification.HarrisLit
