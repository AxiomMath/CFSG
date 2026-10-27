module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat6
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I147
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD147c

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9Cat7Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i264b : I264bAt G p
  list93 : I9List93At G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  list93_3 : I9List93At G 3
  i137_3 : I137At G 3
  i269 : I269At G
  i117 : I117At G
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G


theorem S9Cat7Inputs.toS9Cat6Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ} (h : S9Cat7Inputs G p) :
    S9Cat6Inputs G p where
  i264 := h.i264
  i147 := i147At_of kd147_holds
  i264b := h.i264b
  list93 := h.list93
  i137 := h.i137
  i264_3 := h.i264_3
  i264b_3 := h.i264b_3
  list93_3 := h.list93_3
  i137_3 := h.i137_3
  i269 := h.i269
  i117 := h.i117
  i141 := h.i141
  i2610 := h.i2610
  i107 := h.i107
  i1431 := h.i1431
  table := h.table

theorem ys07_of_cat7_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat7Inputs G p) : YS07 :=
  ys07_of_cat6_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat6Inputs

end CFSG.LocalAnalysis.GLTheoremA
