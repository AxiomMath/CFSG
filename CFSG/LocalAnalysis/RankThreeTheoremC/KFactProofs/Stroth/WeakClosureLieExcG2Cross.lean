module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem crossChevalley_g2 : CrossChevalley .G2 := by
  intro K _ _ ℓ f p _ hadm hp2 hpℓ hmodel
  exact ExcCross.Untw.wcOn_g2_model hadm.1 hp2 hpℓ hadm.2.2.2 hmodel.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
