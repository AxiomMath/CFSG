module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat16
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S9Cat17Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i264b : I264bAt G p
  i137 : I137At G p
  i264b_3 : I264bAt G 3
  i137_3 : I137At G 3
  i141 : I141At G p
  i2610 : I2610At G
  i1431 : I1431ClAt G

structure I107Res : Prop where
  nonab : ChevTwoNonabelian
  inn : Rk2InnRank
  out : OutRank107
  low : TwoRankLowS
  even : CoverEvenAt
  surv : SurvivorLabelCat

section Ys07Cat17


theorem S9Cat17Inputs.toS9Cat15Inputs
    (hI : I107Res) {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S9Cat17Inputs G p) : S9Cat15Inputs G p where
  i264b := h.i264b
  i137 := h.i137
  i264b_3 := h.i264b_3
  i137_3 := h.i137_3
  i141 := h.i141
  i2610 := h.i2610
  i107 := i107At_of_facts (i107LabelAt_holds hI.nonab) (i107AutAt_of_rk2 hI.inn hI.out)
    (i107CoverAt_of_residuals hI.low hI.even) (i107CatAt_of_survivor hI.surv) G p
  i1431 := h.i1431

theorem ys07_of_cat17_inputs
    (h264 : KD264Res) (hInn : CatB.U4InnRest) (hI : I107Res)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat17Inputs G p) : YS07 :=
  ys07_of_cat16_inputs h264 hInn fun G _ _ m hctx p hp => (hin G m hctx p hp).toS9Cat15Inputs hI

end Ys07Cat17

end CFSG.LocalAnalysis.GLTheoremA
