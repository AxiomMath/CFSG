module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat29
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K155XRes
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KU48RMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat30Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  g2field : CatB.KMultA1.G2FieldLayerAt G
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i263 : I263UsedAt G p
  i265 : I265UsedAt G p
  i148d : I148DownAt G
  i158 : I158AtK G
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

section Ys09Cat30

theorem S10Cat30Inputs.toS10Cat29Inputs
    (h155 : I155XRes) (hOdd : CatB.KMultA1.TD4OddNoG2Layer) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S10Cat30Inputs G p) : S10Cat29Inputs G p where
  i155x := i155XAt_of_res h155 G p
  u48res := CatB.KU48R.u48RootResidual_holds G
  multaRes := CatB.KMultA1.multaRes_of_facts (G := G) CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hOdd h.g2field
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i263 := h.i263
  i265 := h.i265
  i148d := h.i148d
  i158 := h.i158
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

end Ys09Cat30

end CFSG.LocalAnalysis.GLTheoremA
