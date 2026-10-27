module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S9.I314
public import CFSG.LocalAnalysis.GLTheoremA.S9.ExtraRep

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9CatInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i183 : Input18_3_4
  i264 : I264At G p
  i91 : I91At G
  i147 : I147At G
  k3 : K3NotChev2At
  i264b : I264bAt G p
  i712 : I712At G p
  list93 : I9List93At G p
  i137 : I137At G p
  sl34 : I71SL34At G
  i264_3 : I264At G 3
  i264b_3 : I264bAt G 3
  i712_3 : I712At G 3
  list93_3 : I9List93At G 3
  i137_3 : I137At G 3
  lbal3 : LBalanceAt G 3
  i269 : I269At G
  i117 : I117At G
  rank23 : Rank23At G
  hy94 : L94TypeHyAt G
  lbal : LBalanceAt G p
  i145 : I145UsedAt G p
  i321 : I321UsedAt G p
  i713 : GL83.I_7_13_1
  i141 : I141At G p
  i2610 : I2610At G
  i67 : I67At G p
  rank3 : Rank3AutAt G
  dickson : InvolvedSL2At G
  i107 : I107At G p
  rank2d4 : Rank2D4At G
  aut : AutRank96At G
  ext : ExtraspecialU5D4At G
  sylow : SylowU38At G
  i81 : I81U5At G
  i2811 : I2811At G
  i102 : I102U4At G
  i112 : I112RkAt G
  i1431 : I1431ClAt G
  table : U4TableAt G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9CatInputs.toS9Inputs (h : S9CatInputs G p) : S9Inputs G p :=
  ⟨h.i183, h.i264, h.i91, h.i147, h.k3, h.i264b, h.i712, h.list93, h.i137, h.sl34, h.i264_3,
    h.i264b_3, h.i712_3, h.list93_3, h.i137_3, h.lbal3, h.i269, h.i117, h.rank23, h.hy94, h.lbal,
    h.i145, h.i321, h.i713, h.i141, h.i2610, h.i67, h.rank3, h.dickson, h.i107, h.rank2d4, h.aut,
    h.ext, h.sylow, i314At_holds, extraspecialRepAt_holds, extraspecialRepCenterAt_holds, h.i81,
    h.i2811, h.i102, h.i112, h.i1431, h.table⟩

theorem ys07_of_cat_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9CatInputs G p) : YS07 :=
  ys07_of_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Inputs

end CFSG.LocalAnalysis.GLTheoremA
