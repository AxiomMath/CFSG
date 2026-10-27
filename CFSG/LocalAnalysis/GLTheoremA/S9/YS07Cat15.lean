module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab6

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat15Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264b : I264bAt G p
  i137 : I137At G p
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G

section Ys07Cat15


theorem S9Cat15Inputs.toS9Cat13Inputs
    (hU : CatB.U4InnRest ∧ CatB.U4OutRest) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat15Inputs G p) : S9Cat13Inputs G p where
  i264b := h.i264b
  i137 := h.i137
  i264b_3 := h.i264b_3
  i137_3 := h.i137_3
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := CatB.u4TableAt_of_residual G hU.1 hU.2

theorem ys07_of_cat15_inputs
    (h264 : KD264Res) (hU : CatB.U4InnRest ∧ CatB.U4OutRest)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat15Inputs G p) : YS07 :=
  ys07_of_cat13_inputs D4YB.d4TwoAutNormInn_holds h264 fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat13Inputs hU

end Ys07Cat15

end CFSG.LocalAnalysis.GLTheoremA
