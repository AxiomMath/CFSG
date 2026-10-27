module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTagsRest
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporCerts
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

section Assembly

theorem kFactWeakClosure_of_tagsRest (h : CrossCharTagsRest) : KFactWeakClosure :=
  kFactWeakClosure_of_inner InnerAction.kFactInnerAction_holds
      (kFactWeakClosureInner_of_cases wcAlt_holds (wcLie_of_crossCharTagsRest h) wcSporadic_holds)

theorem kFactWeakClosure_holds : KFactWeakClosure :=
  kFactWeakClosure_of_tagsRest crossCharTagsRest_holds

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
