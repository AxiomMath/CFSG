module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Levels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S6Cat2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  input14_5 : Input14_5Print
  i1416 : I1416At G p
  chevInner : ChevInnerAt G p
  i71i117 : I71I117At G p
  i196 : I196At G p
  i194 : I194At G p
  chevClosureQ : ChevClosureQAt G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i71u3 : I71U3At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  nonIso : LieTypeNonIsoAt
  i1415 : I1415At G p
  i1415Nine : I1415NineAt G
  i1415Seven : I1415SevenAt G
  i1422 : I1422At G
  i2014 : I2014At G
  i2017 : I2017At G
  i1016Co : I1016CoAt G
  i264ChevTwo : I264ChevTwoAt G p
  i106L62 : I106L62At G
  i131L62 : I131L62At G


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S6Cat2Inputs.toS6CatInputs
    {m : ℕ} (hp : p ∈ Mu G m) (h : S6Cat2Inputs G p) :
    S6CatInputs G p :=
  ⟨lBalanceAt_holds G p hp.1.1, input18_3_4_holds, h.input14_5, h.i1416, h.chevInner, h.i71i117,
    h.i196, h.i194, h.chevClosureQ, h.i2019, h.i248, h.i267, h.i71u3, h.i268, h.i81,
    i112ChevAt_holds G p, h.i2020, h.nonIso, i112StarAt_holds G p, altNotWeakExcAt_holds,
    h.i1415, h.i1415Nine, h.i1415Seven, h.i1422, h.i2014, h.i2017, h.i1016Co, kLevelAltAt_holds,
    i182At_holds G, i71L62At_holds G, h.i264ChevTwo, i61L62At_holds, h.i106L62, h.i131L62⟩

theorem ys05_of_cat2_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S6Cat2Inputs G p) : YS05 :=
  ys05_of_cat_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS6CatInputs hp

end CFSG.LocalAnalysis.GLTheoremA
