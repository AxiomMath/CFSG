module

public import CFSG.LocalAnalysis.GLTheoremA.S10.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KDOutUsers
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Levels
public import CFSG.LocalAnalysis.GLTheoremA.CatA.LieCentreless
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122Holds
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatSingle

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S10CatInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
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
  g2 : TD4G2At G
  perf : TD42PerfAt G
  i264 : I264At G p
  i263 : I263UsedAt G p
  i131 : I131TD4At G
  i265 : I265UsedAt G p
  i91 : I91At G
  i147 : I147At G
  mult : MultU48At G
  i91u : I91U48At G
  i1024 : I1024aU42At G
  i1015u : I1015U42At G
  i8 : I8U48At G
  i2018 : I2018At G
  i91part : I91CentPartAt G p
  aut48 : AutU48At G
  field_n : FieldNAt G p
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


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem catDistinctCtx_holds
    : CatDistinct.Ctx :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds,
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput,
    fun _ _ d hd e => CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e,
    (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
      TauCeti.SporadicName.M22).trans (by decide)⟩

theorem catDistinctAt_holds
    : CatDistinctAt :=
  catDistinctAt_of catDistinctCtx_holds

theorem i112SingleU38At_holds
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) :
    I112SingleU38At G :=
  i112SingleU38At_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
    CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds
    CFSG.HardMathSupport.Solomon.Coordinator.tables112More_holds input18_3_4_holds hsimple hKP
    catDistinctCtx_holds.bridge catDistinctCtx_holds.m22

theorem i112SingleStdAt_holds
    (hsimple : IsSimpleGroup G) (hKP : CFSG.Open.IsKProper G) :
    I112SingleStdAt G :=
  i112SingleStdAt_of_tables CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
    CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds
    CFSG.HardMathSupport.Solomon.Coordinator.tables112More_holds input18_3_4_holds hsimple hKP
    catDistinctCtx_holds.bridge catDistinctCtx_holds.m22

theorem S10CatInputs.toS10Inputs
    {m : ℕ} (hctx : ThmACtx G m) (hp : p ∈ Mu G m)
    (h : S10CatInputs G p) : S10Inputs G p :=
  ⟨input18_3_4_holds, CFSG.HardMathSupport.Solomon.Coordinator.input18_3_12_holds,
    i1131At_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1,
    i1122IsoAt_holds hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp.1.2.1, h.chev2,
    h.dich, h.aut, h.indep, h.cent, h.i148, h.i155, h.i2023, h.i156, h.i2021, h.i91cent, h.u38,
    h.i269, h.lvl, catDistinctAt_holds, h.g2, h.perf, lBalanceAt_holds G 3 Nat.prime_three,
    lBalanceAt_holds G p hp.1.1, h.i264, h.i263, h.i131, h.i265, i712At_holds G p, h.i91, h.i147,
    k3NotChev2At_holds, h.mult, h.i91u, h.i1024, h.i1015u, h.i8, h.i2018, h.i91part, h.aut48,
    h.field_n, i112SingleU38At_holds hctx.1.simple hctx.1.kProper, h.i91type, h.excfield, h.autl3, h.sl3tor, h.i133, h.i148d, h.fieldu48,
    h.i1431, h.i2015, h.i1312, h.i114, h.i1015one, h.i91comp, h.u48, h.u48z, h.i307, h.u48c3,
    h.i158, h.i141, h.su32, h.fieldu3, h.i2811t, h.labels, h.i1015four, h.substable, h.i171, h.u6d0,
    h.i14chev, h.i144one, i112SingleStdAt_holds hctx.1.simple hctx.1.kProper, h.norm113, h.stdf, h.i1428, h.i266, h.i112, h.i1015two,
    h.i263a, h.outcyc, h.inniso, h.i148f, h.i112one, h.multa, h.i91u6, h.fieldpow, h.l2cent,
    h.i1015cover, h.i1015four62, h.u62t9, h.u33, h.fu6exp, g2_center_eq_bot,
    CFSG.StandardType.ChevTwo.ys08_holds⟩

theorem ys09_of_cat_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S10CatInputs G p) : YS09 :=
  ys09_of_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS10Inputs hctx hp

end CFSG.LocalAnalysis.GLTheoremA
