module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat19
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Cat20Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l102_i155x : I155X.I155XAt G p
  i171one : I171OneAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  smallBridge : StdSubSmallAt G
  i1419 : I1419FourAt G
  i141 : I141DynkinAt G
  u42 : U42CatAt G
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

section Ys11Cat20

theorem S12Cat20Inputs.toS12Cat19Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S12Cat20Inputs G p) :
    S12Cat19Inputs G p where
  i171one := h.i171one
  i171two := h.i171two
  i265 := h.i265
  smallBridge := h.smallBridge
  l102_i155 := I155X.i155At_of_X h.l102_i155x
  i1419 := h.i1419
  i141 := h.i141
  u42 := h.u42
  i173 := h.i173
  i172 := h.i172
  compl := h.compl

theorem ys11_of_cat20_inputs
    (hM11 : I1416Rows.I1416SporRow .M 11) (hT : ∀ f : ℕ, 1 ≤ f → TD4InnThreeCentLe f)
    (hR : I1429Residual)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat20Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat19_inputs hM11 hT hR fun G _ _ m hctx hsf h11 p hp =>
    ⟨(hin G m hctx hsf h11 p hp).1.toS12Cat19Inputs, (hin G m hctx hsf h11 p hp).2⟩

end Ys11Cat20

end CFSG.LocalAnalysis.GLTheoremA
