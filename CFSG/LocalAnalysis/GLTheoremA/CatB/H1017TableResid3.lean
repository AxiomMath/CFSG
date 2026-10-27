module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TableResid
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Co1Five

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA


structure I1017ResidualRows3 : Prop where
  b : TwoRankLe 5 .B 2
  mseven : TwoRankLe 7 .M 2
  mthirteen : TwoRankLe 13 .M 2

theorem i1017TableFact_of_residual3 (h : I1017ResidualRows3) : I1017TableFact :=
  i1017TableFact_of_residual4 ⟨twoRankLe_five_co1, h.b, h.mseven, h.mthirteen⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017
