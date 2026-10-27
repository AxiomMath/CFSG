module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.Lemma121Core
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureAlt
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureSporCerts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTagsRest

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank

section Final


theorem kFactWeakClosureInner_holds : Stroth.WeakClosure.KFactWeakClosureInner :=
  Stroth.WeakClosure.kFactWeakClosureInner_of_cases Stroth.WeakClosure.wcAlt_holds
    (Stroth.WeakClosure.wcLie_of_crossCharTagsRest Stroth.WeakClosure.crossCharTagsRest_holds)
    Stroth.WeakClosure.wcSporadic_holds

theorem kFactSylowNormalizerIrreducible_holds : KFactSylowNormalizerIrreducible :=
  kFactSylowNormalizerIrreducible_of_weakClosureInner kFactWeakClosureInner_holds

theorem kFactAbelianSylowRankThree_holds : KFactAbelianSylowRankThree :=
  kFactAbelianSylowRankThree_of_weakClosureInner kFactWeakClosureInner_holds

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank
