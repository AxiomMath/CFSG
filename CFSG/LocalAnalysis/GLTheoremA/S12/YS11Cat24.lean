module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat23
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat24Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  stdCover : StdSubCoverAt G
  l102_i155x : I155X.I155XAt G p
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i1419 : I1419FourAt G
  i141 : I141DynkinAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section Ys11Cat24


theorem S12Cat24Inputs.toS12Cat23Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S12Cat24Inputs G p) :
    S12Cat23Inputs G p where
  stdCover := h.stdCover
  stdInnerD4 := stdSubInnerD4At_holds G
  l102_i155x := h.l102_i155x
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  i1419 := h.i1419
  i141 := h.i141
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

theorem ys11_of_cat24_inputs
    (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) (hR : I1429Residual)
    (hU : CatB.U42Cat.U42SLevel)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat24Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat23_inputs hT hR hU fun G _ _ m hctx hF h11 p hp =>
    ⟨((hin G m hctx hF h11 p hp).1).toS12Cat23Inputs, (hin G m hctx hF h11 p hp).2⟩

end Ys11Cat24

end CFSG.LocalAnalysis.GLTheoremA
