module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat12
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Asm

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat13Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264b : I264bAt G p
  i137 : I137At G p
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G

section Ys07Cat13


theorem S9Cat13Inputs.toS9Cat11Inputs
    (h264 : KD264Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat13Inputs G p) : S9Cat11Inputs G p where
  i264 := i264At_of_res h264 G p
  i264b := h.i264b
  i137 := h.i137
  i264_3 := i264At_of_res h264 G 3
  i264b_3 := h.i264b_3
  i137_3 := h.i137_3
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := h.table

theorem ys07_of_cat13_inputs
    (hD : D4XF.D4TwoAutNormInn) (h264 : KD264Res)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat13Inputs G p) : YS07 :=
  ys07_of_cat12_inputs hD fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat11Inputs h264

end Ys07Cat13

end CFSG.LocalAnalysis.GLTheoremA
