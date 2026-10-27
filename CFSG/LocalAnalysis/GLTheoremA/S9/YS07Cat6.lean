module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD91
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS07I67
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07Rank3Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS07AutRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9Cat6Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264 : I264At G p
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
  i141 : I141At G p
  i2610 : I2610At G
  i107 : I107At G p
  i1431 : I1431ClAt G
  table : U4TableAt G

section ToS9Cat5Inputs


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9Cat6Inputs.toS9Cat5Inputs (h : S9Cat6Inputs G p) : S9Cat5Inputs G p :=
  ⟨h.i264, i91At_holds G, h.i147, h.i264b, h.list93, h.i137, h.i264_3, h.i264b_3, h.list93_3,
    h.i137_3, h.i269, h.i117, h.i141, h.i2610, i67At_holds G p, rank3AutAt_holds G, h.i107,
    CatB.autRank96At_holds G, h.i1431, h.table⟩

end ToS9Cat5Inputs

section YS07Cat6


theorem ys07_of_cat6_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat6Inputs G p) : YS07 :=
  ys07_of_cat5_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat5Inputs

end YS07Cat6

end CFSG.LocalAnalysis.GLTheoremA
