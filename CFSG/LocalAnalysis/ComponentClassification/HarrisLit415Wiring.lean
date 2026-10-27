module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415PS8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415AutD
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415FData
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitL3U3
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsAutPSL2FieldCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsHarrisIdxDischarges
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Outer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

theorem harris415TwoLocalStep_of_schreier
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog) :
    Harris415TwoLocalStep :=
  harris415TwoLocalStep_of_aut hSch autPSL2RCentralizer autPSL2RDerived
    autPSL2InvolutionCentralizer

theorem harris415ComponentStep_of_inputs
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h34 : Harris81Lemma34Input) (h46c : Harris46cInput) (h46d : Harris46dInput)
    (h39 : Harris82TheoremOneKProper) (h36 : Harris81Lemma36NonsimpleInput)
    (hin : Harris36SimpleInput) : Harris415ComponentStep :=
  harris415ComponentStep_of hSch AutL2Facts.autPSL2FieldCentralizer AutL2Facts.cfAutPSL2Centralizer
    h34 h46c h46d h39 h36 hin twoJ2OuterInvolutionIndexFact_holds
    twoHSInnerInvolutionIndexFact_holds GrSLit.L34Facts.outerInvolutionCentralizer
    harris415SmallTypesIndexFact_holds EndB.l3u3InvolutionSL2Fact

theorem harris415Input46e_of_inputs
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (h412 : Harris412Statement) (h47 : Harris47Input) (h34 : Harris81Lemma34Input)
    (h46c : Harris46cInput) (h46d : Harris46dInput) (h39 : Harris82TheoremOneKProper)
    (h36 : Harris81Lemma36NonsimpleInput) (hin : Harris36SimpleInput) : Harris415Input46e :=
  harris415_of_steps h412 h47 (harris415TwoLocalStep_of_schreier hSch)
    (harris415ComponentStep_of_inputs hSch h34 h46c h46d h39 h36 hin)

end CFSG.ComponentClassification.HarrisLit
