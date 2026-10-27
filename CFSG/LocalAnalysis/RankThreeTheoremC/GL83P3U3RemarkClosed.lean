module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

section Closed

theorem gl83GenericPrimeThreeU3RemarkCond_holds_of_heis3 (hHeis3 : KFactWeakClosureHeisThree) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeU3RemarkCond G :=
  fun _ _ _ hS hD1 hU0 => gl83P3U3_remark_of_kfacts hS hD1 hU0
    KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds hHeis3

theorem gl83GenericU3Lemma43E3_holds_of_heis3 (hHeis3 : KFactWeakClosureHeisThree) :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      GL83GenericPrimeThreeU3Lemma43 G :=
  gl83GenericU3Lemma43E3_holds_of_remark_stone
    (gl83GenericPrimeThreeU3RemarkCond_holds_of_heis3 hHeis3)

end Closed

end CFSG.LocalAnalysis.RankThreeTheoremC
