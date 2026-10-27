module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat5
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I147
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147c
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row54
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row48

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S10Cat6Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  dich : FieldDichotomyAt G p
  indep : FieldCentIndepAt G p
  i148 : I148At G
  i155 : I155At G p
  i2023 : I2023At G
  i156 : I156At G p
  i2021 : I2021At G p
  i91cent : I91CentIAt G p
  i269 : I269At G
  g2 : TD4G2At G
  perf : TD42PerfAt G
  i264 : I264At G p
  i263 : I263UsedAt G p
  i131 : I131TD4At G
  i265 : I265UsedAt G p
  i2018 : I2018At G
  i91part : I91CentPartAt G p
  field_n : FieldNAt G p
  i91type : I91TypeAt G
  sl3tor : SL3TorusAt G
  i148d : I148DownAt G
  i1431 : I1431ClAt G
  i2015 : I2015At G p
  i114 : I114At G
  i1015one : I1015oneAt G
  i91comp : I91CompAt G p
  u48 : U48CentInvAt G
  i158 : I158AtK G
  i141 : I141RankAtK G
  su32 : Su32InterAt G
  i1015four : I1015fourAt G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  i1428 : I1428At G
  i266 : I266At G
  i1015two : I1015twoAt G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  outcyc : OutCyclicAt G p
  i148f : I148fiveAt G
  multa : MultAlphaAt G
  i91u6 : I91U6At G
  l2cent : L2CentAt G
  i1015cover : I1015coverAt G
  i1015four62 : I1015fourU62At G
  u62t9 : U62Type9At G


theorem S10Cat6Inputs.toS10Cat5Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S10Cat6Inputs G p) :
    S10Cat5Inputs G p where
  dich := h.dich
  indep := h.indep
  i148 := h.i148
  i155 := h.i155
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i91cent := h.i91cent
  i269 := h.i269
  g2 := h.g2
  perf := h.perf
  i264 := h.i264
  i263 := h.i263
  i131 := h.i131
  i265 := h.i265
  i147 := i147At_of kd147_holds
  i2018 := h.i2018
  i91part := h.i91part
  field_n := h.field_n
  i91type := h.i91type
  sl3tor := h.sl3tor
  i148d := h.i148d
  i1431 := h.i1431
  i2015 := h.i2015
  i114 := h.i114
  i1015one := h.i1015one
  i91comp := h.i91comp
  u48 := h.u48
  u48z := CFSG.LocalAnalysis.GLTheoremA.CatB.U48.u48CentInvFieldAt_holds G
  i158 := h.i158
  i141 := h.i141
  su32 := h.su32
  fieldu3 := fieldU3RestrictAt_holds G
  i1015four := h.i1015four
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  i1428 := h.i1428
  i266 := h.i266
  i1015two := h.i1015two
  i263a := h.i263a
  outcyc := h.outcyc
  i148f := h.i148f
  multa := h.multa
  i91u6 := h.i91u6
  l2cent := h.l2cent
  i1015cover := h.i1015cover
  i1015four62 := h.i1015four62
  u62t9 := h.u62t9

theorem ys09_of_cat6_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S10Cat6Inputs G p) : YS09 :=
  ys09_of_cat5_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Cat5Inputs

end CFSG.LocalAnalysis.GLTheoremA
