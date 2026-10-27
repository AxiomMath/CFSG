module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KDOutUsers
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1131Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122Holds
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.HardMathSupport.Solomon.Coordinator.I713
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

namespace S12

structure Lemma102CatInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  chev2 : Chev2DownAt G p
  dich : FieldDichotomyAt G p
  aut : AutCalcAt G p
  indep : FieldCentIndepAt G p
  cent : CentTD4At G
  i148 : I148At G
  i155 : I155At G p

end S12

structure S12CatInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i145 : I145UsedAt G p
  bal : LBalanceEqAt G p
  chev2 : Chev2DownAt G p
  i171one : I171OneAt G
  rank : RankAutSmallAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
  level2 : LevelTwoAt G
  smallBridge : StdSubSmallAt G
  l102 : S12.Lemma102CatInputs G p
  i112 : I112DiagAt G
  i1419 : I1419FourAt G
  i1416 : I1416TwoAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  i102 : I102InnAt G
  a8 : A8CatAt G
  u42 : U42CatAt G
  trihalf : TriHalfSplitAt G
  i91 : I91FieldAt G p
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

variable {G : Type} [Group G] [Finite G] {p : ℕ}

namespace S12

theorem Lemma102CatInputs.toLemma102Inputs
    (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hKP : CFSG.Open.IsKProper G) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Lemma102CatInputs G p) : Lemma102Inputs G p :=
  ⟨CFSG.LocalAnalysis.GLTheoremA.input18_3_4_holds,
    CFSG.LocalAnalysis.GLTheoremA.i1131At_holds hsimple hnonab hKP hp hp2,
    CFSG.LocalAnalysis.GLTheoremA.i1122IsoAt_holds hsimple hnonab hKP hp hp2,
    h.chev2, h.dich, h.aut, h.indep, h.cent, h.i148, h.i155⟩

end S12

theorem S12CatInputs.toS12Inputs
    {m : ℕ} (hctx : ThmACtx G m) (hsf : StageFacts G m)
    (h11 : Stage11 G m) (hp : p ∈ Mu G m) (h : S12CatInputs G p) : S12Inputs G p := by
  have hp2 : p ≠ 2 := (S12Ctx.of_ctx hctx hsf h11 hp).ctx.ctx.odd
  exact ⟨CFSG.HardMathSupport.Solomon.Coordinator.i_7_13_1_pPrime_holds, h.i145, h.bal,
    CFSG.LocalAnalysis.GLTheoremA.input18_3_4_holds, h.chev2, h.i171one, h.rank, h.i171two,
    h.i265, h.i269, h.i269six, h.level2, h.smallBridge,
    CFSG.LocalAnalysis.GLTheoremA.lBalanceAt_holds G p hp.1.1,
    h.l102.toLemma102Inputs hctx.1.simple hctx.1.nonabelian hctx.1.kProper hp.1.1 hp2, h.i112,
    h.i1419, h.i1416, h.i141, h.i1429, h.i102, h.a8, h.u42, h.trihalf, h.i91,
    fun S _ h1 h2 => CatDistinct.field_u42_a6
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds S h1 h2,
    CFSG.HardMathSupport.Solomon.Coordinator.input18_10_holds,
    CFSG.LocalAnalysis.GLTheoremA.i712At_holds G p, h.i173, h.i172, h.compl⟩

theorem ys11_of_cat_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12CatInputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_inputs fun G _ _ m hctx hsf h11 p hp =>
    ⟨(hin G m hctx hsf h11 p hp).1.toS12Inputs hctx hsf h11 hp, (hin G m hctx hsf h11 p hp).2⟩

end CFSG.LocalAnalysis.GLTheoremA
