module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.YS03Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I1810
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I1933
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4.LBalanceBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {G : Type} [Group G] [Finite G]

theorem s4SInputs_of_schreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h145 : GWLBalanceClause3) {p : ℕ} (hp : p.Prime) (h1912 : I1912At) (h1913 : I1913At)
    (h2027 : I2027At) (h264 : I264At G p) (h91 : I91At G) (h147 : I147At G)
    (h1016 : I1016At G) (h71 : I71M12At G) (h1426 : I1426At G p) : S4SInputs G p where
  lBalance := lBalanceAt_of_catalogueSchreier hS hp
  input18_3_4 := CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hS
  i1810 := i1810UsedAt_of_schreier hS G p
  input14_5 := input14_5Print_of_gw h145
  i1912 := h1912
  i1933 := i1933At_holds G p
  i1913 := h1913
  i2027 := h2027
  i264 := h264
  i91 := h91
  i147 := h147
  i1016 := h1016
  i71m12 := h71
  i1426 := h1426

theorem ys03_of_schreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h145 : GWLBalanceClause3) (h1912 : I1912At) (h1913 : I1913At) (h2027 : I2027At)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m,
      I264At G p ∧ I91At G ∧ I147At G ∧ I1016At G ∧ I71M12At G ∧ I1426At G p) : YS03 :=
  ys03_of_inputs fun G _ _ m hctx p hp =>
    let h := hin G m hctx p hp
    s4SInputs_of_schreier hS h145 hp.1.1 h1912 h1913 h2027 h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2

end CFSG.LocalAnalysis.GLTheoremA
