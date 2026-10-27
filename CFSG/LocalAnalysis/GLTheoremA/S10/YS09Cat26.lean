module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat25
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2018Res : Prop where
  b : CFSG.HardMathSupport.Solomon.Coordinator.YS08.SporL3Down TauCeti.SporadicName.B
  m : CFSG.HardMathSupport.Solomon.Coordinator.YS08.SporL3Down TauCeti.SporadicName.M
  odd : I2018.I2018OddB3
  char : I2018.I2018U38Char2
  notAlt : I2018.I2018U38NotAlt
  cover : I2018.I2018U38Cover
  bt : I2018.I2018BorelTits
  core : I2018.I2018ChevCore

structure S10Cat26Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i155x : I155X.I155XAt G p
  u48res : U48RootResidual G
  multaRes : CatB.MultA3.MultAG2Residual G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i148d : I148DownAt G
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

section Ys09Cat26

theorem S10Cat26Inputs.toS10Cat25Inputs
    (hI : I2018Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat26Inputs G p) : S10Cat25Inputs G p where
  i155x := h.i155x
  u48res := h.u48res
  multaRes := h.multaRes
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i2018 := I2018.i2018At_of_facts (G := G) hI.b hI.m hI.odd hI.char hI.notAlt hI.cover hI.bt hI.core
  i148d := h.i148d
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

end Ys09Cat26

end CFSG.LocalAnalysis.GLTheoremA
