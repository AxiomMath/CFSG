module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U42
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U48
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U33
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09U38R
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S10Cat2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  chev2 : Chev2DownAt G p
  dich : FieldDichotomyAt G p
  aut : AutCalcAt G p
  indep : FieldCentIndepAt G p
  cent : CentTD4At G
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
  i91 : I91At G
  i147 : I147At G
  i91u : I91U48At G
  i1024 : I1024aU42At G
  i8 : I8U48At G
  i2018 : I2018At G
  i91part : I91CentPartAt G p
  field_n : FieldNAt G p
  i91type : I91TypeAt G
  excfield : ExcNoFieldAt G
  sl3tor : SL3TorusAt G
  i133 : I133At G p
  i148d : I148DownAt G
  fieldu48 : FieldU48At G
  i1431 : I1431ClAt G
  i2015 : I2015At G p
  i1312 : I1312At G p
  i114 : I114At G
  i1015one : I1015oneAt G
  i91comp : I91CompAt G p
  u48 : U48CentInvAt G
  u48z : U48CentInvFieldAt G
  i307 : I307At G
  u48c3 : U48Cent3AtK G
  i158 : I158AtK G
  i141 : I141RankAtK G
  su32 : Su32InterAt G
  fieldu3 : FieldU3RestrictAt G
  i2811t : I2811TAt G
  labels : LabelDictAt
  i1015four : I1015fourAt G
  substable : StdSubTableAt G
  i171 : I171At G
  u6d0 : U6D0RankAt G
  i14chev : I1431Chev2At G
  i144one : I144oneAt G
  stdf : StdSubFAt G
  i1428 : I1428At G
  i266 : I266At G
  i112 : I112NormAt G
  i1015two : I1015twoAt G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  outcyc : OutCyclicAt G p
  inniso : InnDiagIsoAt G p
  i148f : I148fiveAt G
  multa : MultAlphaAt G
  i91u6 : I91U6At G
  l2cent : L2CentAt G
  i1015cover : I1015coverAt G
  i1015four62 : I1015fourU62At G
  u62t9 : U62Type9At G
  fu6exp : FieldU6ExpAt G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S10Cat2Inputs.toS10CatInputs
    {m : ℕ} (hctx : ThmACtx G m) (h : S10Cat2Inputs G p) :
    S10CatInputs G p where
  chev2 := h.chev2
  dich := h.dich
  aut := h.aut
  indep := h.indep
  cent := h.cent
  i148 := h.i148
  i155 := h.i155
  i2023 := h.i2023
  i156 := h.i156
  i2021 := h.i2021
  i91cent := h.i91cent
  u38 := u38RankAt_holds G
  i269 := h.i269
  lvl := levelU38At_holds G
  g2 := h.g2
  perf := h.perf
  i264 := h.i264
  i263 := h.i263
  i131 := h.i131
  i265 := h.i265
  i91 := h.i91
  i147 := h.i147
  mult := multU48At_holds G
  i91u := h.i91u
  i1024 := h.i1024
  i1015u := i1015U42At_holds G
  i8 := h.i8
  i2018 := h.i2018
  i91part := h.i91part
  aut48 := autU48_holds G
  field_n := h.field_n
  i91type := h.i91type
  excfield := h.excfield
  autl3 := autL3At_holds G
  sl3tor := h.sl3tor
  i133 := h.i133
  i148d := h.i148d
  fieldu48 := h.fieldu48
  i1431 := h.i1431
  i2015 := h.i2015
  i1312 := h.i1312
  i114 := h.i114
  i1015one := h.i1015one
  i91comp := h.i91comp
  u48 := h.u48
  u48z := h.u48z
  i307 := h.i307
  u48c3 := h.u48c3
  i158 := h.i158
  i141 := h.i141
  su32 := h.su32
  fieldu3 := h.fieldu3
  i2811t := h.i2811t
  labels := h.labels
  i1015four := h.i1015four
  substable := h.substable
  i171 := h.i171
  u6d0 := h.u6d0
  i14chev := h.i14chev
  i144one := h.i144one
  norm113 := i113NormAt_holds G hctx.1.simple hctx.1.kProper
  stdf := h.stdf
  i1428 := h.i1428
  i266 := h.i266
  i112 := h.i112
  i1015two := h.i1015two
  i263a := h.i263a
  outcyc := h.outcyc
  inniso := h.inniso
  i148f := h.i148f
  i112one := i112OneAt_holds G hctx.1.simple hctx.1.kProper
  multa := h.multa
  i91u6 := h.i91u6
  fieldpow := fieldAutPowClosedAt_holds
  l2cent := h.l2cent
  i1015cover := h.i1015cover
  i1015four62 := h.i1015four62
  u62t9 := h.u62t9
  u33 := u33SolvCentAt_holds G
  fu6exp := h.fu6exp

theorem ys09_of_cat2_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S10Cat2Inputs G p) : YS09 :=
  ys09_of_cat_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10CatInputs hctx

end CFSG.LocalAnalysis.GLTheoremA
