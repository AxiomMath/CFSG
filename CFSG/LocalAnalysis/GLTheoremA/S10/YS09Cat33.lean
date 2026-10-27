module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat32
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I2023Res : Prop where
  rank : I2023.I2023FactD4RankTwo
  out : I2023.I2023FactOutCyclic
  c1 : I2023.I2023FactC1
  odd : I2023.I2023FactD2LocalOdd
  even : I2023.I2023FactD4BorelEven

structure S10Cat33Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  g2field : CatB.KMultA1.G2FieldLayerAt G
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

section Ys09Cat33

theorem S10Cat33Inputs.toS10Cat32Inputs
    (h23 : I2023Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat33Inputs G p) : S10Cat32Inputs G p where
  g2field := h.g2field
  i2023 := I2023.i2023At_of_facts G h23.rank h23.out h23.c1 h23.odd h23.even
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

end Ys09Cat33

end CFSG.LocalAnalysis.GLTheoremA
