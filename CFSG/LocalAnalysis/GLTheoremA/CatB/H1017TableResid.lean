module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017TableMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017J3McL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA


structure I1017ResidualRows4 : Prop where
  co1 : TwoRankLe 5 .Co1 2
  b : TwoRankLe 5 .B 2
  mseven : TwoRankLe 7 .M 2
  mthirteen : TwoRankLe 13 .M 2

theorem i1017TableFact_of_residual4 (h : I1017ResidualRows4) : I1017TableFact :=
  i1017TableFact_of_residual ⟨twoRankLe_three_j3, twoRankLe_three_mcl, h.co1, h.b, h.mseven,
    h.mthirteen⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017
