module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Wiring
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInv
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly47Lit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitTheorem1Simple

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harris415Input46e_of_literature
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h219 : Harris82Lemma219Input) (hSD : Harris46SemidihedralInput)
    (hQI : Harris46QuaternionInput)
    (hT1 : Harris82Theorem1KProper) (h311 : Harris311PSL2Input) (h9 : Harris81Lemma34NineInput)
    (h35 : Harris81Lemma35Step) (hCI : GSLit.ClassicalInvolutionInput)
    (hP2 : Harris81Lemma33Simple) (hT2 : Harris82Theorem2SLTwo) (hF : L4U4ThreeInvolutionFacts)
    (h36 : Harris81Lemma36NonsimpleInput) (hin : Harris36SimpleInput) : Harris415Input46e :=
  have h34 : Harris81Lemma34Input := harris81Lemma34Input_of h311 h9
  have hGA : TBLit.GriessMultipliersOdd := TBLit.griessMultipliersOdd_holds
  have hGC : TBLit.GriessMultipliersCentralCovers :=
    @CFSG.Milestones.cl_lit_griess_schur_multipliers_central_covers
  harris415Input46e_of_inputs hSch
    (harris412_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
        (harris46c_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch h219 hSD)
        (harris46d_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch h219 hSD
            hGA hGC hCI h34)
        (harris46eOdd_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch h219 hSD
            hGA hGC hCI h34)
        (harris46g_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch hQI))
    (harris47_of_literature h219 hSD hGC hT1 h311 h9 h35 hCI hP2 hT2 hF
      GrSLit.L34Facts.l34CoverInvolutionFact) h34
    (harris46c_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch h219 hSD)
    (harris46d_of AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer hSch h219 hSD hGA
      hGC hCI h34) (harris82TheoremOneKProper_of hGA hT1) h36 hin

end CFSG.ComponentClassification.HarrisLit
