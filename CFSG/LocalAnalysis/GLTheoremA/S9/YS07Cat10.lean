module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat9
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269T

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat10Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i264b : I264bAt G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i117 : I117At G
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G

section Ys07Cat10


theorem S9Cat10Inputs.toS9Cat8Inputs
    (h269 : I269Residual3) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat10Inputs G p) : S9Cat8Inputs G p where
  i264 := h.i264
  i264b := h.i264b
  i137 := h.i137
  i264_3 := h.i264_3
  i264b_3 := h.i264b_3
  i137_3 := h.i137_3
  i269 := i269At_of_residual3 h269 G
  i117 := h.i117
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := h.table

theorem ys07_of_cat10_inputs
    (h269 : I269Residual3) (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat10Inputs G p) : YS07 :=
  ys07_of_cat9_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat8Inputs h269

end Ys07Cat10

end CFSG.LocalAnalysis.GLTheoremA
