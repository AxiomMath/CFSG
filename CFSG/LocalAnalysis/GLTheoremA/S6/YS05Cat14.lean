module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat13

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S6Cat14Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i2017Lie : I2017LieAt G
  i196 : I196At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  i1422Char2 : I1422Char2At G
  i264ChevTwo : I264ChevTwoAt G p

section Ys05Cat14

theorem S6Cat14Inputs.toS6Cat13Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h3 : NoTrialityCharThreeAt G)
    (h : S6Cat14Inputs G p) : S6Cat13Inputs G p where
  i2017Lie := h.i2017Lie
  charThree := h3
  i196 := h.i196
  i2019 := h.i2019
  i248 := h.i248
  i267 := h.i267
  i268 := h.i268
  i81 := h.i81
  i2020 := h.i2020
  i1422Char2 := h.i1422Char2
  i264ChevTwo := h.i264ChevTwo

end Ys05Cat14

end CFSG.LocalAnalysis.GLTheoremA
