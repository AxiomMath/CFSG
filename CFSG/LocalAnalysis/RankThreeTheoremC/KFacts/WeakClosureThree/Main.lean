module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Spor
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Outer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieAll
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.GL83PartI.I713.Final

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open WeakClosureThree

section Main


theorem kFactWeakClosureOmega3_holds
    : KFactWeakClosureOmega3 :=
  kFactWeakClosureOmega3_of_dich KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds
    GL83.I713.i_7_13_1_holds KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    (dichThree_of_cases dichThreeAlt_holds dichThreeLie_holds dichThreeSpor_holds)

theorem kFactWeakClosureHeisThree_holds
    : KFactWeakClosureHeisThree :=
  kFactWeakClosureHeisThree_of_heis KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds
    GL83.I713.i_7_13_1_holds KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    outerThreeInner_holds
    (heisDichThree_of_cases dichThreeAlt_holds heisDichThreeLie_holds dichThreeSpor_holds)

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC
