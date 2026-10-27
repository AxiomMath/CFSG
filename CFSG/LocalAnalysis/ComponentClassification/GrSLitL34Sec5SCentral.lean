module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SMoves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5CentralCard510

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma510CentralStep_of_moves
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hComp : L34Cor217ComponentStep) :
    L34Lemma510CentralStep := by
  intro G _ _ L t S T hset hexp hΩ hZnc _ _ _
  exact (false_of_moves_center hS hU hheld hSol hGW hMax hL34 h58 h59 hSC hComp hset hexp hΩ
    hZnc).elim

theorem l34Lemma510CentralCardStep_of_moves
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hComp : L34Cor217ComponentStep) :
    L34Lemma510CentralCardStep :=
  l34Lemma510CentralCardStep_of_centralStep hS hU hheld hSol hGW hMax hL34
    (l34Lemma510CentralStep_of_moves hS hU hheld hSol hGW hMax hL34 h58 h59 hSC hComp)

end CFSG.ComponentClassification.GrSLit.GrS5S
