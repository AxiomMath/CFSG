module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat18
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat19Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i137 : I137At G p
  i137_3 : I137At G 3
  i141 : I141At G p
  i2610 : I2610At G
  i1431 : I1431ClAt G

section Ys07Cat19


theorem S9Cat19Inputs.toS9Cat17Inputs
    (hR : I264bResidual) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat19Inputs G p) : S9Cat17Inputs G p where
  i264b := i264bAt_of_residual (fun hp Y _ _ => lBalanceAt_holds Y p hp) hR
  i137 := h.i137
  i264b_3 := i264bAt_of_residual (fun hp Y _ _ => lBalanceAt_holds Y 3 hp) hR
  i137_3 := h.i137_3
  i141 := h.i141
  i2610 := h.i2610
  i1431 := h.i1431

theorem ys07_of_cat19_inputs
    (h264 : KD264Res) (hInn : CatB.U4InnRest) (hI : I107Res2) (hR : I264bResidual)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat19Inputs G p) : YS07 :=
  ys07_of_cat18_inputs h264 hInn hI fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat17Inputs hR

end Ys07Cat19

end CFSG.LocalAnalysis.GLTheoremA
