module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma43
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.Level

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S4Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  input18_3_4 : Input18_3_4
  i1131 : I1131At G p
  i1122 : I1122IsoAt G p
  i1132 : I1132UsedAt G p
  i1412 : I1412UsedAt G p
  lBalance : LBalanceAt G p
  listedMultiplier : ListedMultiplierBound p
  hatMultiplier : HatOddMultiplierBound

variable {G : Type} [Group G] [Finite G]

theorem stage4Order_of_inputs {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m)
    (hS3 : Stage3 G p) (hin : S4Inputs G p) : Stage4Order G p := by
  have hc : S4Ctx G p := ⟨hp.1.1, hctx.1.simple, hctx.1.nonabelian, hctx.1.kProper,
    hin.input18_3_4, hin.i1131, hin.i1122⟩
  exact stage4Order_of hc hp.1.2.1
    (lemma43 hp.1.1 hS3 hin.input18_3_4 hctx.1.kProper hctx.1.simple hctx.1.nonabelian hin.i1131
      hin.i1122 hin.i1132 hin.lBalance)
    (lemma47 hp.1.1 hp.1.2.1 hin.input18_3_4 hctx.1.kProper hctx.1.simple hctx.1.nonabelian)
    (lemma49_of_levelCoincidence hin.listedMultiplier hin.hatMultiplier hp.1.1 hp.1.2.1
      hin.input18_3_4 hctx.1.kProper hctx.1.simple hctx.1.nonabelian hin.i1412 hin.i1122
      hin.lBalance)

theorem ys02_of_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S4Inputs G p) : YS02 :=
  fun G _ _ m hctx p hp hS3 => stage4Order_of_inputs hctx hp hS3 (hin G m hctx p hp)

end CFSG.LocalAnalysis.GLTheoremA
