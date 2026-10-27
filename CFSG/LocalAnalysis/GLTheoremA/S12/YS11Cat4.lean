module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I112
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I91

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Cat4Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  chev2 : Chev2DownAt G p
  i171one : I171OneAt G
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
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section YS11Cat4

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S12Cat4Inputs.toS12Cat3Inputs
    (h : S12Cat4Inputs G p) : S12Cat3Inputs G p :=
  ⟨h.chev2, h.i171one, rank_holds G, h.i171two, h.i265, h.i269, h.i269six, h.smallBridge, h.l102,
    h.i112, h.i1419, h.i1416, h.i141, h.i1429, h.i102, h.a8, h.u42, trihalf_holds G, i91_holds G p,
    h.i173, h.i172, h.compl⟩

theorem ys11_of_cat4_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat4Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat3_inputs fun G _ _ m hctx hsf h11 p hp =>
    ⟨(hin G m hctx hsf h11 p hp).1.toS12Cat3Inputs, (hin G m hctx hsf h11 p hp).2⟩

end YS11Cat4

end CFSG.LocalAnalysis.GLTheoremA
