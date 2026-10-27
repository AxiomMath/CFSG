module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat10
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XAsm2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat11Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i264b : I264bAt G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G

structure YS07Tables : Prop where
  i269 : I269Residual3
  d4 : D4XF.D4TwoAutNormInn

section Ys07Cat11


theorem S9Cat11Inputs.toS9Cat10Inputs
    (hS : YS07Tables) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat11Inputs G p) : S9Cat10Inputs G p where
  i264 := h.i264
  i264b := h.i264b
  i137 := h.i137
  i264_3 := h.i264_3
  i264b_3 := h.i264b_3
  i137_3 := h.i137_3
  i117 := D4T.i117At_of_autNorm hS.d4 G
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := h.table

theorem ys07_of_cat11_inputs
    (hS : YS07Tables) (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat11Inputs G p) : YS07 :=
  ys07_of_cat10_inputs hS.i269 fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat10Inputs hS

end Ys07Cat11

end CFSG.LocalAnalysis.GLTheoremA
