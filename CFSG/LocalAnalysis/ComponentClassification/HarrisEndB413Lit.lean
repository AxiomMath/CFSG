module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB413J2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEnd413L34d
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndB413L3U3
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Main
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly47Lit
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSD46B

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harris413Input46e_of_literature
    (hCI : GSLit.ClassicalInvolutionInput)
    (hT1 : Harris82Theorem1KProper) (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput)
    (h35 : Harris81Lemma35Step) (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo)
    (hF : L4U4ThreeInvolutionFacts)
    (hin : Harris36SimpleInput) : Harris413Input46e :=
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
  harris413_of_cases hin h412 h47 (EndB.harris413_J2 AutL2Facts.autPSL2FieldCentralizer
      AutL2Facts.cfAutPSL2Centralizer AutL2Facts.cfAutPSL2Involution AutL2Facts.cfAutPSL2Fusion)
          (harris413_L34 AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
              AutL2Facts.cfAutPSL2Involution AutL2Facts.cfAutPSL2Fusion)
    (EndB.harris413_L3U3 hSch AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
      AutL2Facts.cfAutPSL2Involution hGA harris82Lemma219Input_holds h35
      alternatingCoverInvolutionFact_holds)
    (EndB.harris413_L2 AutL2Facts.cfAutPSL2Sylow AutL2Facts.cfAutPSL2Centralizer
        AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Fusion)

end CFSG.ComponentClassification.HarrisLit
