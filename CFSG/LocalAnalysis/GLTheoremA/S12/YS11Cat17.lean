module

public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat16
public import CFSG.HardMathSupport.Dickson.BMRows.KFormRowsBM
public import CFSG.HardMathSupport.Dickson.BMRows.KFormBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269R6
public import CFSG.LocalAnalysis.GLTheoremA.S12.YS11Cat6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10

section Ys11Cat17

theorem S12Cat7Inputs.toS12Cat6InputsK
    (hK : CFSG.HardMathSupport.Dickson.BMRows.I1416TwoSporSK) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S12Cat7Inputs G p) : S12Cat6Inputs G p :=
  ⟨h.i171one, h.i171two, h.i265, h.i269, h.i269six, h.smallBridge, h.l102_dich, h.l102_indep, h.l102_i148,
    h.l102_i155, h.i1419, CFSG.HardMathSupport.Dickson.BMRows.i1416TwoAt_of_sporSK hK G, h.i141, h.i1429, h.u42,
    h.i173, h.i172, h.compl⟩

theorem S12Cat16Inputs.toS12Cat7Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : S12Cat16Inputs G p) : S12Cat7Inputs G p :=
  (((h.toS12Cat14Inputs.toS12Cat12Inputs D4YB.d4TwoAutNormInn_holds).toS12Cat10Inputs
    i269Residual3_holds).toS12Cat8Inputs).toS12Cat7Inputs hp hp2

theorem ys11_of_cat17_inputs
    (hM11 : I1416Rows.I1416SporRow .M 11)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Cat16Inputs G p ∧ S12CanonInputs G p) : YS11 :=
  ys11_of_cat6_inputs fun G _ _ m hctx hsf h11 p hp =>
    ⟨((hin G m hctx hsf h11 p hp).1.toS12Cat7Inputs hp.1.1 hp.1.2.1).toS12Cat6InputsK
      (CFSG.HardMathSupport.Dickson.BMRows.i1416TwoSporSK_of_rows hM11), (hin G m hctx hsf h11 p hp).2⟩

end Ys11Cat17

end CFSG.LocalAnalysis.GLTheoremA
