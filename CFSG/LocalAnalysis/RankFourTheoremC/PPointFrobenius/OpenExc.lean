module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.KC.Discharge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CatalogSchreier
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.PPrimeCompInvolution
public import CFSG.LocalAnalysis.RankThreeTheoremC.CoprimeAutFromPPrime
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius


theorem ysPPointFrobenius_of_open_exc
    (hI : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure)
    (hR : ExcFiveResiduals) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointFrobenius :=
  ysPPointFrobenius_of_kfacts
    ⟨hI, hW, stronglyEmbeddedPSL2KFact_of_excFiveResiduals hR,
      CFSG.LocalAnalysis.RankThreeTheoremC.kFactCoprimeAutEvenCentralizer_of_pPrimeCompP
        CFSG.AGLEmbedding.KFactProofs.PPrimeComp.kFactPPrimeCompInvolutionP_holds,
      CFSG.AGLEmbedding.kFactCatalogSchreier⟩

section Weak


theorem ysPPointFrobenius_of_weak_exc
    (hW : CFSG.LocalAnalysis.RankThreeTheoremC.KFactWeakClosure)
    (hR : ExcFiveResiduals) :
    CFSG.Yardstones.Md8ed6d263d89.YSPPointFrobenius :=
  ysPPointFrobenius_of_open_exc
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.kFactInnerAction_holds hW hR

end Weak

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
