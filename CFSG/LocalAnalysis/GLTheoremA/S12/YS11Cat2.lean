module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS11A

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Cat2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i145 : I145UsedAt G p
  chev2 : Chev2DownAt G p
  i171one : I171OneAt G
  rank : RankAutSmallAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
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

theorem S12Cat2Inputs.toS12CatInputs
    (h : S12Cat2Inputs G p) : S12CatInputs G p :=
  ⟨h.i145, lBalanceEqAt_holds G p, h.chev2, h.i171one, h.rank, h.i171two, h.i265, h.i269, h.i269six,
    levelTwoAt_holds G, h.smallBridge, h.l102, h.i112, h.i1419, h.i1416, h.i141, h.i1429, h.i102,
    h.a8, h.u42, h.trihalf, h.i91, h.i173, h.i172, h.compl⟩

theorem ys11_of_cat2_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat2Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat_inputs fun G _ _ m hctx hsf h11 p hp =>
    ⟨(hin G m hctx hsf h11 p hp).1.toS12CatInputs, (hin G m hctx hsf h11 p hp).2⟩

end CFSG.LocalAnalysis.GLTheoremA
