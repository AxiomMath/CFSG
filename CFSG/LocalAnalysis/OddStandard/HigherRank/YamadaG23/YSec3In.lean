module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YBundle
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCert
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31Fin
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusion32
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFusion33
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTrFin

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three

section Certified

theorem sec3Inputs_of : Sec3Inputs := by
  have hC : CentreDvdThree := centreDvdThree_of
  have hOdd : OddCentre := oddCentre_of
  have hOut : OutTwo := outTwo_of
  have h31 : Fusion31 := fusion31_of hOdd hOut
  have hDef : Fusion3Def := fusion3Def_of h31 hOdd hOut
  have h32 : Fusion32 := fusion32_of h31 hOdd hOut
  have hT : YTransport := ytransport_of hC hOut
  exact ⟨h31, hDef, h32, fusion33_of h31 hDef h32 hOdd hOut hT, hOdd, hOut, hT⟩

end Certified

end CFSG.OddStandard.HigherRank.YamadaG23
