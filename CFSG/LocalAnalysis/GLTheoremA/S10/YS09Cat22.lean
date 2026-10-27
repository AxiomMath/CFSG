module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat21
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat22Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i155x : I155X.I155XAt G p
  u48res : U48RootResidual G
  multaRes : CatB.MultA3.MultAG2Residual G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i2018 : I2018At G
  i148d : I148DownAt G
  i1431 : I1431ClAt G
  i2015 : I2015At G p
  i114 : I114At G
  i158 : I158AtK G
  i141 : I141RankAtK G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i148f : I148fiveAt G
  u62t9 : U62Type9At G

section Ys09Cat22


theorem S10Cat22Inputs.toS10Cat21Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S10Cat22Inputs G p) :
    S10Cat21Inputs G p where
  u48res := h.u48res
  multaRes := h.multaRes
  i155 := I155X.i155At_of_X h.i155x
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i2018 := h.i2018
  i148d := h.i148d
  i1431 := h.i1431
  i2015 := h.i2015
  i114 := h.i114
  i158 := h.i158
  i141 := h.i141
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := h.i148f
  u62t9 := h.u62t9

theorem ys09_of_cat22_inputs
    (h264 : KD264Res) (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) (hD : I91T.TD4C1NotExc)
    (hO : I1015OneRes)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat22Inputs G p) : YS09 :=
  ys09_of_cat21_inputs h264 hT hD hO fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat21Inputs

end Ys09Cat22

end CFSG.LocalAnalysis.GLTheoremA
