module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat17
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015E6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I131T4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat18Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i148 : I148At G
  i155 : I155At G p
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i2018 : I2018At G
  i91type : I91TypeAt G
  sl3tor : SL3TorusAt G
  i148d : I148DownAt G
  i1431 : I1431ClAt G
  i2015 : I2015At G p
  i114 : I114At G
  i1015one : I1015oneAt G
  u48 : U48CentInvAt G
  i158 : I158AtK G
  i141 : I141RankAtK G
  su32 : Su32InterAt G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  outcyc : OutCyclicAt G p
  i148f : I148fiveAt G
  multa : MultAlphaAt G
  i91u6 : I91U6At G
  u62t9 : U62Type9At G

section Ys09Cat18


theorem S10Cat18Inputs.toS10Cat17Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S10Cat18Inputs G p) :
    S10Cat17Inputs G p where
  i148 := h.i148
  i155 := h.i155
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i131 := i131TD4At_holds G
  i265 := h.i265
  i2018 := h.i2018
  i91type := h.i91type
  sl3tor := h.sl3tor
  i148d := h.i148d
  i1431 := h.i1431
  i2015 := h.i2015
  i114 := h.i114
  i1015one := h.i1015one
  u48 := h.u48
  i158 := h.i158
  i141 := h.i141
  su32 := h.su32
  i1015four := i1015fourAt_holds G
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i1015two := i1015twoAt_holds G
  i263a := h.i263a
  outcyc := h.outcyc
  i148f := h.i148f
  multa := h.multa
  i91u6 := h.i91u6
  i1015cover := i1015coverAt_holds G
  i1015four62 := i1015fourU62At_holds G
  u62t9 := h.u62t9

theorem ys09_of_cat18_inputs
    (h264 : KD264Res)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat18Inputs G p) : YS09 :=
  ys09_of_cat17_inputs h264 fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat17Inputs

end Ys09Cat18

end CFSG.LocalAnalysis.GLTheoremA
