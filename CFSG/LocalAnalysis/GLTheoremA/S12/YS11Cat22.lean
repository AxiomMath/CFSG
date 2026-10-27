module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat21
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U42CatMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S12Cat22Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l102_i155x : I155X.I155XAt G p
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  smallBridge : StdSubSmallAt G
  i1419 : I1419FourAt G
  i141 : I141DynkinAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section Ys11Cat22


theorem S12Cat22Inputs.toS12Cat20Inputs
    (hU : CatB.U42Cat.U42SLevel) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S12Cat22Inputs G p) : S12Cat20Inputs G p where
  l102_i155x := h.l102_i155x
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  smallBridge := h.smallBridge
  i1419 := h.i1419
  i141 := h.i141
  u42 := CatB.U42Cat.u42CatAt_of_sLevel hU G
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

theorem ys11_of_cat22_inputs
    (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f) (hR : I1429Residual)
    (hU : CatB.U42Cat.U42SLevel)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat22Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat21_inputs hT hR fun G _ _ m hctx hF h11 p hp =>
    ⟨((hin G m hctx hF h11 p hp).1).toS12Cat20Inputs hU, (hin G m hctx hF h11 p hp).2⟩

end Ys11Cat22

end CFSG.LocalAnalysis.GLTheoremA
