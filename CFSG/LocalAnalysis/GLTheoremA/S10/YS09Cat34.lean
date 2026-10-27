module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat33
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2018Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2018Res2 : Prop where
  b : CFSG.HardMathSupport.Solomon.Coordinator.YS08.SporL3Down TauCeti.SporadicName.B
  m : CFSG.HardMathSupport.Solomon.Coordinator.YS08.SporL3Down TauCeti.SporadicName.M
  odd : I2018.I2018OddB3
  cover : I2018.I2018U38Cover
  core : I2018.I2018ChevCore

structure S10Cat34Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i158 : I158AtK G
  i171 : I171At G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i148f : I148fiveAt G

section Ys09Cat34

theorem S10Cat34Inputs.toS10Cat33Inputs
    (hG2F : CatB.KG2F.G2FieldLayerS) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat34Inputs G p) : S10Cat33Inputs G p where
  g2field := CatB.KG2F.g2FieldLayerAt_of_fact (G := G) hG2F
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i158 := h.i158
  i171 := h.i171
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := h.i148f

end Ys09Cat34

end CFSG.LocalAnalysis.GLTheoremA
