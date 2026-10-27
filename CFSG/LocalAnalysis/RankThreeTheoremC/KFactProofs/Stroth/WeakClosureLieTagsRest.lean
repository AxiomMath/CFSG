module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsl
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsp
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePsu
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmega
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieReeG2Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcG2Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcF4Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE6Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE7Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE8Cross
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwD4
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwE6
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwRee
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTits

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

structure CrossCharTagsRest : Prop where
  twistedF4 : CrossReeTits .twistedF4

section Assembly

theorem crossCharTags_of_rest (h : CrossCharTagsRest) : CrossCharTags :=
  ⟨crossClassical_psl, crossClassical_psu, crossClassical_psp, crossClassical_pomegaOdd,
    crossClassical_pomegaPlus, crossClassical_pomegaMinus, crossChevalley_g2, crossChevalley_f4,
    crossChevalley_e6, crossChevalley_e7, crossChevalley_e8, ExcCross.crossChevalley_twistedE6,
    ExcCross.crossChevalley_trialityD4, crossReeTits_twistedG2, h.twistedF4, crossReeTits_tits⟩

theorem wcLie_of_crossCharTagsRest (h : CrossCharTagsRest) : WCLie :=
  wcLie_of_crossCharTags (crossCharTags_of_rest h)

theorem crossCharTagsRest_holds : CrossCharTagsRest :=
  ⟨ExcCross.crossReeTits_twistedF4⟩

end Assembly

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
