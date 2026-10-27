module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YHyp

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open CFSG.OddStandard.HigherRank.G2Three

structure Sec3Inputs : Prop where
  f31 : Fusion31
  fDef : Fusion3Def
  f32 : Fusion32
  f33 : Fusion33
  oddCentre : OddCentre
  outTwo : OutTwo
  transport : YTransport

end CFSG.OddStandard.HigherRank.YamadaG23
