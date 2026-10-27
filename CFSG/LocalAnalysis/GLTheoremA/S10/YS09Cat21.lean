module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat20
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015OneRes
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X5
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48X6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S10Cat21Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  u48res : U48RootResidual G
  multaRes : CatB.MultA3.MultAG2Residual G
  i155 : I155At G p
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

@[expose] def I1015OneRes : Prop :=
  CatB.I1015OneRes.I1015oneSp4Inner ∧ CatB.I1015OneRes.I1015oneSp4Out ∧ CatB.I1015OneRes.I1015oneU3Rank

section Ys09Cat21


theorem S10Cat21Inputs.toS10Cat20Inputs
    (hO : I1015OneRes) {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : S10Cat21Inputs G p) : S10Cat20Inputs G p where
  multaRes := h.multaRes
  i155 := h.i155
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
  i1015one := CatB.I1015OneRes.i1015oneAt_of_residuals hO.1 hO.2.1 hO.2.2 G
  u48 := CatB.U48.X6.u48CentInvAt_of_root G h.u48res
  i158 := h.i158
  i141 := h.i141
  su32 := CatB.U48.X5.su32InterAt_holds G
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i263a := h.i263a
  outcyc := OutCyc.outCyclicAt_holds (Or.inl ⟨hp, hp2⟩)
  i148f := h.i148f
  u62t9 := h.u62t9

theorem ys09_of_cat21_inputs
    (h264 : KD264Res) (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) (hD : I91T.TD4C1NotExc)
    (hO : I1015OneRes)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat21Inputs G p) : YS09 :=
  ys09_of_cat20_inputs h264 hT hD fun G _ _ m hctx p hp =>
    (hin G m hctx p hp).toS10Cat20Inputs hO hp.1.1 hp.1.2.1

end Ys09Cat21

end CFSG.LocalAnalysis.GLTheoremA
