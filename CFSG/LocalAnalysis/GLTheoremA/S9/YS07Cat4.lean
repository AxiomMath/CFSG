module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9Cat4Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
  i91 : I91At G
  i147 : I147At G
  i264b : I264bAt G p
  list93 : I9List93At G p
  i137 : I137At G p
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  list93_3 : I9List93At G 3
  i137_3 : I137At G 3
  i269 : I269At G
  i117 : I117At G
  i145 : I145UsedAt G p
  i141 : I141At G p
  i2610 : I2610At G
  i67 : I67At G p
  rank3 : Rank3AutAt G
  i107 : I107At G p
  aut : AutRank96At G
  i1431 : I1431ClAt G
  table : U4TableAt G

section ToS9Cat3


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9Cat4Inputs.toS9Cat3Inputs (h : S9Cat4Inputs G p) : S9Cat3Inputs G p :=
  ⟨h.i264, h.i91, h.i147, h.i264b, h.list93, h.i137, h.i264_3, h.i264b_3, h.list93_3, h.i137_3,
    h.i269, h.i117, CatB.rank23At_holds G, h.i145, h.i141, h.i2610, h.i67, h.rank3, h.i107, h.aut,
    CatB.extraspecialTD4At_holds G, h.i1431, h.table⟩

end ToS9Cat3

section YS07Final


theorem ys07_of_cat4_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat4Inputs G p) : YS07 :=
  ys07_of_cat3_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat3Inputs

end YS07Final

end CFSG.LocalAnalysis.GLTheoremA
