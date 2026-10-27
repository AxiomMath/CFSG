module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcE7

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem crossChevalley_e7 : CrossChevalley .E7 := by
  intro K _ _ ℓ f p _ hadm hp2 hpℓ hmodel
  exact ExcCross.Untw.wcOn_e7_model hadm.1 hp2 hpℓ hmodel.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
