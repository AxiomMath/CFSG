module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcF4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint


theorem crossChevalley_f4 : CrossChevalley .F4 := by
  intro K _ _ ℓ f p _ hadm hp2 hpℓ hmodel
  exact ExcCross.Untw.wcOn_f4_model hadm.1 hp2 hpℓ hmodel.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
