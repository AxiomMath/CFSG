module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.LocalAnalysis.GLTheoremA.S10

structure S12Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i713 : CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime
  i145 : I145UsedAt G p
  bal : LBalanceEqAt G p
  i183 : Input18_3_4
  chev2 : Chev2DownAt G p
  i171one : I171OneAt G
  rank : RankAutSmallAt G
  i171two : I171TwoAt G
  i265 : I265StdAt G p
  i269 : I269At G
  i269six : I269SixAt G
  level2 : LevelTwoAt G
  smallBridge : StdSubSmallAt G
  lbal : LBalanceAt G p
  l102 : Lemma102Inputs G p
  i112 : I112DiagAt G
  i1419 : I1419FourAt G
  i1416 : I1416TwoAt G
  i141 : I141DynkinAt G
  i1429 : I1429At G
  i102 : I102InnAt G
  a8 : A8CatAt G
  u42 : U42CatAt G
  trihalf : TriHalfSplitAt G
  i91 : I91FieldAt G p
  disj : SmallDisjointAt
  i1810 : Input18_10
  i712 : I712At G p
  i173 : I173At G
  i172 : I172At G
  compl : Compl123At G p

theorem S12Inputs.toInputs123 {G : Type} [Group G] [Finite G] {p : ℕ} (h : S12Inputs G p) : Inputs123 G p :=
  ⟨⟨⟨⟨h.i713, h.i145, h.bal, h.i183, h.chev2, h.i171one⟩, h.rank, h.i171two, h.i265, h.i269, h.i269six, h.level2,
      h.smallBridge, h.lbal⟩, h.l102, h.i112, h.i1419, h.i1416, h.i141, h.i1429, h.i102, h.a8, h.u42, h.trihalf,
      h.i91, h.disj⟩, h.i1810, h.i712, h.i173, h.i172, h.compl⟩

structure S12CanonInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  rank3 : RankThreeLabelAt G
  canon : S12.CanonNbrAt G p

open S12 in
theorem ys11_of_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → StageFacts G m → Stage11 G m →
      ∀ p ∈ Mu G m, S12Inputs G p ∧ S12CanonInputs G p) : YS11 := by
  intro G _ _ m hctx hsf h11 p hp B x L hS hsplit
  obtain ⟨hI0, hC⟩ := hin G m hctx hsf h11 p hp
  have hc : S12Ctx G m p := S12Ctx.of_ctx hctx hsf h11 hp
  have hI := hI0.toInputs123
  have hsplit16 : SplitInnerDiagMarking16 p B L :=
    splitInnerDiag16_of_canon (rankLabel_of_canon hc hS hsplit hC.rank3) hsplit
  refine ⟨fun y J hnb => prop122_marking_canon hc hS hsplit hC.rank3 hC.canon hI.l122 hnb, fun D K hstd => ?_⟩
  have hcfg : Cfg12 G m p B x L D K := ⟨hc, ⟨hS, hsplit16⟩, hstd⟩
  exact ⟨prop123 hcfg hI, fun d hd hd1 => odd_canon hcfg hI.to124 hd hd1⟩

end CFSG.LocalAnalysis.GLTheoremA
