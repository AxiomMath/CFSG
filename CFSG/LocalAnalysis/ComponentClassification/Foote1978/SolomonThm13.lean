module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76HbOddLieLeaves
public import CFSG.LocalAnalysis.ComponentClassification.GSYard01
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13HResiduesB
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.ComponentClassification.FooteLit

section Certificates

theorem solomonThm13Simple_holds
    :
    Sol76T13.SolomonThm13Simple :=
  Sol76T13.solomonThm13Simple_of_schreier
    CFSG.RankThree.PartOne.SPOR.schreierFor_catalog
    (Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves
      Sol76.Sig.GSYard03.lemma39TwoDiscK2At_solRestrictedHub_holds
      Sol76.Sig.GSYard02.quasisimpleSylowFourJoinedSCN_holds
      Sol76.Sig.GSYard03.solomonQTwoDisconnectedSylowInvFor_holds)

end Certificates

end CFSG.ComponentClassification.FooteLit
