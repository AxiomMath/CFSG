module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107EExc
public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat20

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I107Res4 : Prop where
  inn : Rk2InnRank
  out : OutRank107
  lowExcRest : I107E.TwoRankLowExcRest
  even : CoverEvenAt

section Ys07Cat22

theorem I107Res4.toI107Res3
    (h : I107Res4) : I107Res3 :=
  ⟨h.inn, h.out, I107E.twoRankLowExc_of_X h.lowExcRest, h.even⟩

end Ys07Cat22

end CFSG.LocalAnalysis.GLTheoremA
