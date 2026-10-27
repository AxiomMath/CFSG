module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Prop91

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S9

structure S9Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
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
  i314 : I314At
  repA : ExtraspecialRepAt
  repB : ExtraspecialRepCenterAt
  i81 : I81U5At G
  i2811 : I2811At G
  i102 : I102U4At G
  i112 : I112RkAt G
  i1431 : I1431ClAt G
  table : U4TableAt G

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S9Inputs.toL93 (h : S9Inputs G p) : Lemma93Inputs G p :=
  ⟨h.i183, h.i264, h.i91, h.i147, h.k3, h.i264b, h.i712, h.list93, h.i137, h.sl34⟩

theorem S9Inputs.toL93three (h : S9Inputs G p) : Lemma93Inputs G 3 :=
  ⟨h.i183, h.i264_3, h.i91, h.i147, h.k3, h.i264b_3, h.i712_3, h.list93_3, h.i137_3, h.sl34⟩

theorem S9Inputs.toL94 (h : S9Inputs G p) : Lemma94Inputs G :=
  ⟨h.toL93three, h.lbal3, h.i269, h.i117, h.rank23, h.hy94⟩

theorem S9Inputs.toL95 (h : S9Inputs G p) : Lemma95Inputs G p :=
  ⟨h.toL93, h.lbal, h.i145, h.i321, h.i713, h.i141, h.i2610, h.i67, h.rank3, h.dickson, h.i269⟩

theorem S9Inputs.toL96 (h : S9Inputs G p) : Lemma96Inputs G p :=
  ⟨h.toL94, h.i107, h.rank2d4, h.aut, h.ext, h.sylow, h.i314, h.repA, h.repB⟩

theorem S9Inputs.toClosing (h : S9Inputs G p) : ClosingInputs G :=
  ⟨h.rank23, h.i81, h.i2811, h.i102, h.i183, h.i112, h.i1431, h.table⟩

theorem S9Inputs.toProp92 (h : S9Inputs G p) : Prop92Inputs G p :=
  ⟨h.toL95, h.toL96, h.toClosing⟩

theorem stage9_of_inputs (hc : S9Ctx G p) (hin : S9Inputs G p) : Stage9 G p :=
  ⟨fun _ _ _ h => prop91 hc hin.toProp92 h,
    fun _ _ _ hB hx hx1 hcomp hnorm hcent hchev halt =>
      prop92 hc hin.toProp92 ⟨hB, hx, hx1, hcomp, hnorm, hcent, hchev, halt⟩⟩

theorem ys07_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S9Inputs G p) : YS07 := by
  intro G _ _ m hctx p hp h3 h4o h4 h5 h6 h7 h8
  exact stage9_of_inputs (S9Ctx.of_ctx hctx hp h3 h4o h4 h5 h6 h7 h8) (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA
