module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Prop101

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S10Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i183x : Input18_3_12
  i1131 : I1131At G p
  i1122 : I1122IsoAt G p
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
  u38 : U38RankAt G
  i269 : I269At G
  lvl : LevelU38At G
  dist : CatDistinctAt
  g2 : TD4G2At G
  perf : TD42PerfAt G
  lbal3 : LBalanceAt G 3
  lbal : LBalanceAt G p
  i264 : I264At G p
  i263 : I263UsedAt G p
  i131 : I131TD4At G
  i265 : I265UsedAt G p
  i712 : I712At G p
  i91 : I91At G
  i147 : I147At G
  k3 : K3NotChev2At
  mult : MultU48At G
  i91u : I91U48At G
  i1024 : I1024aU42At G
  i1015u : I1015U42At G
  i8 : I8U48At G
  i2018 : I2018At G
  i91part : I91CentPartAt G p
  aut48 : AutU48At G
  field_n : FieldNAt G p
  single38 : I112SingleU38At G
  i91type : I91TypeAt G
  excfield : ExcNoFieldAt G
  autl3 : AutL3At G
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
  single_std : I112SingleStdAt G
  norm113 : I113NormAt G
  stdf : StdSubFAt G
  i1428 : I1428At G
  i266 : I266At G
  i112 : I112NormAt G
  i1015two : I1015twoAt G
  i263a : 4 ≤ GLATwoLocalRank 3 G → I263AlphaAt G
  outcyc : OutCyclicAt G p
  inniso : InnDiagIsoAt G p
  i148f : I148fiveAt G
  i112one : I112OneAt G
  multa : MultAlphaAt G
  i91u6 : I91U6At G
  fieldpow : FieldAutPowClosedAt
  l2cent : L2CentAt G
  i1015cover : I1015coverAt G
  i1015four62 : I1015fourU62At G
  u62t9 : U62Type9At G
  u33 : U33SolvCentAt G
  fu6exp : FieldU6ExpAt G
  g2c : G2CentrelessAt
  ys08 : YS08

namespace S10Inputs

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem setup (h : S10Inputs G p) : SetupInputs G p :=
  ⟨h.aut, h.dich, h.indep, h.cent, h.i2023, h.i156, h.i2021, h.i91cent, h.u38, h.i269, h.lbal3, h.lvl, h.i91, h.i147,
    h.g2, h.perf⟩

theorem l102 (h : S10Inputs G p) : Lemma102Inputs G p :=
  ⟨h.i183, h.i1131, h.i1122, h.chev2, h.dich, h.aut, h.indep, h.cent, h.i148, h.i155⟩

theorem l103 (h : S10Inputs G p) : Lemma103Inputs G p :=
  ⟨h.aut, h.l102, h.i264, h.i263, h.i131, h.i265, h.i712, h.i91, h.i147, h.k3, h.mult, h.i91u, h.i1024,
    h.i1015u, h.i8, h.i2018, h.i91part, h.lbal3, h.i183, h.i183x, h.aut48, h.field_n, h.g2, h.single38,
    ⟨h.i91type, h.excfield, h.autl3, h.sl3tor⟩, h.dist⟩

theorem l104 (h : S10Inputs G p) : Lemma104Inputs G p :=
  ⟨h.l102, h.i133, h.i148d, h.fieldu48, h.i1431, h.i183, h.lbal⟩

theorem l105 (h : S10Inputs G p) : Lemma105Inputs G p :=
  ⟨h.l103, h.l104, h.i2015, h.i1312, h.i114, h.i1015one, h.i1131, h.i1122, h.lbal, h.i91comp⟩

theorem alpha (h : S10Inputs G p) : AlphaInputs G p :=
  ⟨h.l105, h.i1428, h.i266, h.i112, h.i1015two, h.i263a, h.i158, h.outcyc, h.inniso, h.i148f, h.i112one, h.multa,
    h.i91u6, h.fieldpow, h.l2cent, h.i1015cover, h.i1015four62, h.u62t9, h.u33, h.fu6exp, h.g2c⟩

theorem beta (h : S10Inputs G p) : BetaInputs G p :=
  ⟨h.l105, h.u48, h.u48z, h.i307, h.u48c3, h.i158, h.i141, h.su32, h.fieldu3, h.fieldpow⟩

theorem gamma (h : S10Inputs G p) : GammaInputs G p :=
  ⟨h.l105, h.u48, h.u48z, h.i2811t, h.ys08, h.labels, h.i1015four, h.substable, h.i171, h.u6d0, h.i14chev, h.i144one,
    h.dist, h.single_std, h.norm113, h.stdf⟩

end S10Inputs

theorem prop101_of_inputs {G : Type} [Group G] [Finite G] {p : ℕ} (hc : S10Ctx G p) (hin : S10Inputs G p) :
    Concl101 G p :=
  prop101 hc hin.setup hin.l103 hin.alpha hin.beta hin.gamma

theorem ys09_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S10Inputs G p) : YS09 := by
  intro G _ _ m hctx hsf p hp
  exact (concl101_iff G p).1 (prop101_of_inputs (S10Ctx.of_ctx hctx hsf hp) (hin G m hctx p hp))

end CFSG.LocalAnalysis.GLTheoremA
