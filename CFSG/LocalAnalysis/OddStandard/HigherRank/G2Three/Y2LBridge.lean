module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LT1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LHS
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LT3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LAut
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Final
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NN2

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

theorem y2l_sec7NT (hB : YamadaG23.Sec3Inputs) : YamadaG23.Sec7NT :=
  YamadaG23.sec7NT_holds hB aut29Idx_holds

section Sec62


theorem y2l_sec62' (hB : YamadaG23.Sec3Inputs) : YamadaG23.Sec62' :=
  YamadaG23.sec62'_of hB lemma26Pres2_holds lemma26HS_holds lemma27G23_holds

end Sec62

end CFSG.OddStandard.HigherRank.G2Three.Sec2
