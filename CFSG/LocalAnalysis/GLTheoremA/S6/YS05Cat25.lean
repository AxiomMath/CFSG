module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFFCenterL62
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFFRankCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2017LRes2 : Prop where
  cls : I2017LieClassification
  noA7 : I2017LieNoA7
  rank : I2017LieRank


section Ys05Cat25


theorem ys05_of_cat25_inputs
    (hR : D3A4Regular) (hN : D3CaseTwoOne)
    (hRes : I264bResidual2) (hS1 : I1422Lie2Fact) (h17 : I2017LRes2) (h20 : I2020Res) (h248 : I248Res) (h81 : I81Res)
    (h196 : I196Res)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S6Cat23Inputs G p) : YS05 :=
  ys05_of_cat24_inputs hR hN hRes hS1 ⟨h17.cls, h17.noA7, h17.rank, I2017LieCenterL62_holds, I2017LieRankCenter_holds⟩
    h20 h248 h81 h196 h

end Ys05Cat25

end CFSG.LocalAnalysis.GLTheoremA
