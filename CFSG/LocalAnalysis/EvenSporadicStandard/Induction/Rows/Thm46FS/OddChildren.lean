module

public import CFSG.LocalAnalysis.ComponentClassification.HeldBalSwappedCIT
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76HbOddLieLeaves
public import CFSG.LocalAnalysis.ComponentClassification.GSYard01
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.EvenSporadicStandard.Induction

theorem heldKSwapped_of_milestones
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels) :
    CFSG.ComponentClassification.GrSLit.HeldKSwapped :=
  CFSG.ComponentClassification.GrSLit.heldKSwapped_of_cit hCIT
    (CFSG.ComponentClassification.Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves
      CFSG.ComponentClassification.Sol76.Sig.GSYard03.lemma39TwoDiscK2At_solRestrictedHub_holds
      CFSG.ComponentClassification.Sol76.Sig.GSYard02.quasisimpleSylowFourJoinedSCN_holds
      CFSG.ComponentClassification.Sol76.Sig.GSYard03.solomonQTwoDisconnectedSylowInvFor_holds)

end CFSG.EvenSporadicStandard.Induction
