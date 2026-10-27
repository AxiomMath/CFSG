module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat7
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat8Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i264b : I264bAt G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i269 : I269At G
  i117 : I117At G
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G

section YS07Cat8


theorem S9Cat8Inputs.toS9Cat7Inputs
    (hL : I9List93Residual) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat8Inputs G p) : S9Cat7Inputs G p where
  i264 := h.i264
  i264b := h.i264b
  list93 := i9List93At_of_residual G p
      (listedMultiplierBound_of_tables
          CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
          sporadicMultiplierTable_holds p)
      (hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds) (CatB.rank23At_holds G) hL
  i137 := h.i137
  i264_3 := h.i264_3
  i264b_3 := h.i264b_3
  list93_3 := i9List93At_of_residual G 3
      (listedMultiplierBound_of_tables
          CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
          sporadicMultiplierTable_holds 3)
      (hatOddMultiplierBound_of_tables sporadicMultiplierTable_holds) (CatB.rank23At_holds G) hL
  i137_3 := h.i137_3
  i269 := h.i269
  i117 := h.i117
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := h.table

theorem ys07_of_cat8_inputs
    (hL : I9List93Residual) (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ),
    ThmACtx G m → ∀ p ∈ Mu G m, S9Cat8Inputs G p) : YS07 :=
  ys07_of_cat7_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat7Inputs hL

end YS07Cat8

end CFSG.LocalAnalysis.GLTheoremA
