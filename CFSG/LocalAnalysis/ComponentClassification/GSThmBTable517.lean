module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516Inner
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBSections
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aConjFix

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.UnbalancedCorr

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor) in
theorem conjFixStatement_of_inputs (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput) :
    ConjFixStatement :=
  fun _ _ _ h _ hg he hP => h.conj_fix hS hU hheld hg he hP

theorem table517Statement_of_inputs (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hCFi : CFProp23IndexElim)
    (hSol : SolomonTwoSubgroupAltInput) (hHS : HarrisSolomonA7Input) (hST : SuzukiTausskyInput)
    (hHe : CFHeNoA5) (hP23 : CFProp23L34) (hRank : CFL34CoverRank) (hOut : CFL34CoverOut)
    (hAut : CFAutL2Rank) (hP21 : CFProp21A10) (hLoc : CFA10Local) (hNO : CFA10NoOuter)
    (hFus : CFProp23Row516) (hStab : CFAutL2Stab) (hCent : CF516Cent)
    (hZ : CFRow516InnerCenter) (hFusI : CFRow516InnerFusion) (hTK : CFRow516InnerT)
    (hOutI : CFRow516InnerOut) (hPSp : CFRow516InnerPSp) (hNoPSp : CFRow516NoPSp)
    (hInv : CFL2InvPair) (hOS5 : Row516CentralizerStatement) (hsec : SectionStatement) :
    Table517Statement :=
  table517_of_inputs hB1 hCF23 hCF24 hCFc hCFi hSol hHS hST hHe hP23 hRank hOut hAut hP21 hLoc
    hNO hsec (elim516_of_catalogue hB1 sylowKernelStatement embedsTQuotStatement hCF23 hCF24 hCFc
        hCFi hST hFus hStab hCent hZ hFusI hTK hOutI hPSp hNoPSp hInv hOS5 hsec)

end CFSG.ComponentClassification.GSThmB
