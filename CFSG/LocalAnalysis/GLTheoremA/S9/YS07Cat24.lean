module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat22
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XExc2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I107Res5 : Prop where
  inn : Rk2InnRank
  out : OutRank107
  lowExcRest2 : I107X.TwoRankLowExcRest2
  even : CoverEvenAt

section Ys07Cat24

theorem I107Res5.toI107Res4
    (h : I107Res5) : I107Res4 :=
  ⟨h.inn, h.out, I107X.twoRankLowExcRest_of_X2 h.lowExcRest2, h.even⟩

end Ys07Cat24

end CFSG.LocalAnalysis.GLTheoremA
