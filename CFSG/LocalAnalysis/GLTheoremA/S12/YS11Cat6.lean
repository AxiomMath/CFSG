module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2Down
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS11A8

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Cat6Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
  smallBridge : StdSubSmallAt G
  l102_dich : FieldDichotomyAt G p
  l102_indep : FieldCentIndepAt G p
  l102_i148 : I148At G
  l102_i155 : I155At G p
  i1419 : I1419FourAt G
  i1416 : I1416TwoAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  u42 : U42CatAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section YS11Cat6

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S12Cat6Inputs.toS12Cat5Inputs
    (h : S12Cat6Inputs G p) : S12Cat5Inputs G p :=
  ⟨chev2DownAt_holds (G := G) p, h.i171one, h.i171two, h.i265, h.i269, h.i269six, h.smallBridge,
    chev2DownAt_holds (G := G) p, h.l102_dich, h.l102_indep, h.l102_i148, h.l102_i155, h.i1419, h.i1416,
    h.i141, h.i1429, CatB.a8CatAt_holds G, h.u42, h.i173, h.i172, h.compl⟩

theorem ys11_of_cat6_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat6Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat5_inputs fun G _ _ m hctx hsf h11 p hp =>
    ⟨(hin G m hctx hsf h11 p hp).1.toS12Cat5Inputs, (hin G m hctx hsf h11 p hp).2⟩

end YS11Cat6

end CFSG.LocalAnalysis.GLTheoremA
