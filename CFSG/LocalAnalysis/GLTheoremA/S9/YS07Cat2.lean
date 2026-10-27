module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I112a
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KDOutUsers
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Levels
public import CFSG.LocalAnalysis.GL83PartI.I713.Final

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9Cat2Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
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
  rank23 : Rank23At G
  hy94 : L94TypeHyAt G
  i145 : I145UsedAt G p
  i141 : I141At G p
  i2610 : I2610At G
  i67 : I67At G p
  rank3 : Rank3AutAt G
  i107 : I107At G p
  rank2d4 : Rank2D4At G
  aut : AutRank96At G
  ext : ExtraspecialU5D4At G
  sylow : SylowU38At G
  i81 : I81U5At G
  i2811 : I2811At G
  i102 : I102U4At G
  i1431 : I1431ClAt G
  table : U4TableAt G


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9Cat2Inputs.toS9CatInputs
    {m : ℕ} (hp : p ∈ Mu G m) (h : S9Cat2Inputs G p) :
    S9CatInputs G p :=
  ⟨input18_3_4_holds, h.i264, h.i91, h.i147, k3NotChev2At_holds, h.i264b, i712At_holds G p,
    h.list93, h.i137, i71SL34At_holds G, h.i264_3, h.i264b_3, i712At_holds G 3, h.list93_3,
    h.i137_3, lBalanceAt_holds G 3 Nat.prime_three, h.i269, h.i117, h.rank23, h.hy94,
    lBalanceAt_holds G p hp.1.1, h.i145, i321UsedAt_holds p, GL83.I713.i_7_13_1_holds, h.i141,
    h.i2610, h.i67, h.rank3, involvedSL2At_holds G, h.i107, h.rank2d4, h.aut, h.ext, h.sylow,
    h.i81, h.i2811, h.i102, i112RkAt_holds G, h.i1431, h.table⟩

theorem ys07_of_cat2_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Cat2Inputs G p) : YS07 :=
  ys07_of_cat_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9CatInputs hp

end CFSG.LocalAnalysis.GLTheoremA
