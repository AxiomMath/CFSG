module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop61
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma63
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma64
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop71

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S6Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  lBalance : LBalanceAt G p
  input18_3_4 : Input18_3_4
  input14_5 : Input14_5Print
  i1416 : I1416At G p
  chevInner : ChevInnerAt G p
  i71i117 : I71I117At G p
  i196 : I196At G p
  i194 : I194At G p
  chevClosureQ : ChevClosureQAt G p
  i183Diag : I183DiagAt G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i71u3 : I71U3At G p
  i268 : I268At G p
  i81 : I81At G p
  i112Chev : I112ChevAt G p
  i2020 : I2020At G p
  nonIso : LieTypeNonIsoAt
  i112Star : I112StarAt G p
  altNotWeakExc : AltNotWeakExcAt
  i1415 : I1415At G p
  i2013 : I2013At
  i203 : I203At
  i1415Nine : I1415NineAt G
  i1415Seven : I1415SevenAt G
  i1422 : I1422At G
  i2014 : I2014At G
  i2017 : I2017At G
  i1016Co : I1016CoAt G
  kLevelAlt : KLevelAltAt
  i182 : I182At G
  i2prod : I2ProdAt G
  i71L62 : I71L62At G
  i264ChevTwo : I264ChevTwoAt G p
  i61L62 : I61L62At
  i106L62 : I106L62At G
  i131L62 : I131L62At G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace S6Inputs

theorem toProp61 (h : S6Inputs G p) : Prop61Inputs G p :=
  ⟨h.lBalance, h.chevInner, h.i71i117, h.i196, h.i194⟩

theorem toLemma62 (h : S6Inputs G p) : Lemma62Inputs G p :=
  ⟨h.lBalance, h.input18_3_4, h.input14_5, h.i1416, h.chevClosureQ, h.i183Diag, h.i2019⟩

theorem toLemma63 (h : S6Inputs G p) : Lemma63Inputs G p := ⟨h.i248⟩

theorem toLemma64 (h : S6Inputs G p) : Lemma64Inputs G p := ⟨h.i267, h.i71u3⟩

theorem toProp65 (h : S6Inputs G p) : Prop65Inputs G p :=
  ⟨h.i268, h.i81, h.i112Chev, h.i2020, h.i1416, h.input18_3_4, h.nonIso⟩

theorem toLemma72 (h : S6Inputs G p) : Lemma72Inputs G p :=
  ⟨h.input18_3_4, h.i112Star, h.altNotWeakExc, h.i1415, h.i2013⟩

theorem toLemma73 (h : S6Inputs G p) : Lemma73Inputs G p :=
  ⟨h.input18_3_4, h.i112Star, h.altNotWeakExc, h.i2013, h.i203, h.i1415Nine, h.i1415Seven, h.i1422,
    h.i2014, h.i2017, h.i1016Co, h.kLevelAlt, h.i182, h.i2prod, h.i106L62, h.i71L62⟩

theorem toProp71 (h : S6Inputs G p) : Prop71Inputs G p :=
  ⟨h.i264ChevTwo, h.i61L62, h.i106L62, h.i131L62, h.i182⟩

end S6Inputs

theorem stage6_of_inputs {m : ℕ} (hctx : ThmACtx G m) (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (hS4 : Stage4 G p) (hS5 : Stage5 G p) (hin : S6Inputs G p) :
    Stage6 G p := by
  have hc := S6Ctx.of_ctx hctx hp hS3 hS4o hS4 hS5
  have h61 : Prop61At G p := prop61_holds hc hin.toProp61
  have h62 : Lemma62At G p := lemma62_holds hc hin.toLemma62
  have h63 : Lemma63At G p := lemma63_holds hc hin.toLemma63 h62
  have h64 : Lemma64At G p := lemma64_holds hc hin.toLemma64 h62 h63
  have h65 : Prop65At G p := prop65_holds hc hin.toProp65 h61 h62 h64
  intro B x L h q hq hq2
  by_cases hqp : q = p
  · subst hqp
    exact h61 B x L h
  · exact h65 q hq hq2 hqp B x L h

theorem stage7_of_inputs {m : ℕ} (hctx : ThmACtx G m) (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (hS4 : Stage4 G p) (hS5 : Stage5 G p) (hin : S6Inputs G p) :
    Stage7 G p := by
  have hc := S6Ctx.of_ctx hctx hp hS3 hS4o hS4 hS5
  have hset : AltSetupAt G p := altSetup_holds hc
  have h72 : Lemma72At G p := lemma72_holds hc hin.toLemma72
  have h73 : Lemma73At G p := lemma73_holds hc hin.toLemma73 h72
  exact prop71_holds hc hin.toProp71 hset h73

theorem ys05_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S6Inputs G p) : YS05 :=
  fun G _ _ m hctx p hp hS3 hS4o hS4 hS5 =>
    ⟨stage6_of_inputs hctx hp hS3 hS4o hS4 hS5 (hin G m hctx p hp),
      stage7_of_inputs hctx hp hS3 hS4o hS4 hS5 (hin G m hctx p hp)⟩

end CFSG.LocalAnalysis.GLTheoremA
