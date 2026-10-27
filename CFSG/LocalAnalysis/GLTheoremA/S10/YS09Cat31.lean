module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat30
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTRed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KSubTDistinct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure SubTRes : Prop where
  u5 : KSubT.CompFact S9.isU5two S9.isU4two
  u6 : KSubT.CompFact S9.isU6two (fun i => S9.isU4two i ∨ S9.isU5two i ∨ S10.isL2eight i)
  sp8 : KSubT.CompFactSp8
  d4 : KSubT.CompFact S9.isD4two S9.isU4two

structure S10Cat31Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  g2field : CatB.KMultA1.G2FieldLayerAt G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i148d : I148DownAt G
  i158 : I158AtK G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  i1428 : I1428At G
  i266 : I266At G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  i148f : I148fiveAt G
  u62t9 : U62Type9At G

section Ys09Cat31

theorem S10Cat31Inputs.toS10Cat30Inputs
    (hsub : SubTRes) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S10Cat31Inputs G p) : S10Cat30Inputs G p where
  g2field := h.g2field
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i148d := h.i148d
  i158 := h.i158
  substable := KSubT.substable_of_facts hsub.u5 hsub.u6 hsub.sp8 hsub.d4 KSubT.listDistinct_holds G
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  i148f := h.i148f
  u62t9 := h.u62t9

end Ys09Cat31

end CFSG.LocalAnalysis.GLTheoremA
