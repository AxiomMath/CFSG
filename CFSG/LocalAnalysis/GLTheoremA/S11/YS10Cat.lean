module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Reduction
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U5R
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1122Holds
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S11CatInputs (G : Type) [Group G] [Finite G] : Prop where
  i161a : I161aAt G
  i161b : I161bAt G
  i162 : I162At G
  i163 : I163At G
  i164 : I164At G
  i165 : I165At G
  i2315a : I2315aAt G
  i2315b : I2315bAt G
  e62 : E62At G
  chev2 : ∀ p : ℕ, Chev2DownAt G p
  idiag : InnDiagIndepAt G
  i166 : I166At G
  labUniq : LabelUniqAt G
  eTable : ETableAt G
  i61 : I61At G
  i1441 : I1441At G
  i14neg : I14NegAt G
  i1416 : I1416Chev2At G
  i142 : I142At G
  rank3 : RankThreeLabelAt G
  u64types : U64TypesAt G
  u5rank : U5RankAt
  u6struct : U6StructAt G
  u5case : U5CaseAt G
  u6case : U6CaseAt G
  centq : CentQuasiAt G

variable {G : Type} [Group G] [Finite G]

theorem S11CatInputs.toS11Inputs
    {m : ℕ} (hctx : ThmACtx G m) (h : S11CatInputs G) : S11Inputs G :=
  ⟨h.i161a, h.i161b, h.i162, h.i163, h.i164, h.i165, h.i2315a, h.i2315b,
    CFSG.LocalAnalysis.GLTheoremA.i3013_holds G, h.e62,
    CFSG.LocalAnalysis.GLTheoremA.input18_3_4_holds,
    CFSG.HardMathSupport.Solomon.Coordinator.input18_10_holds, h.chev2,
    fun _ hp hp2 => CFSG.LocalAnalysis.GLTheoremA.i1122IsoAt_holds hctx.1.simple hctx.1.nonabelian
      hctx.1.kProper hp hp2,
    h.idiag, h.i166, h.labUniq, h.eTable, h.i61, h.i1441, h.i14neg, h.i1416, h.i142,
    CFSG.AGLEmbedding.kFactCatalogSchreier_holds,
    CFSG.HardMathSupport.Solomon.Coordinator.input2_5_proved, h.rank3,
    CFSG.StandardType.ChevTwo.ys08_holds, h.u64types, h.u5rank,
    CFSG.LocalAnalysis.GLTheoremA.u5out_holds G, h.u6struct, h.u5case, h.u6case, h.centq⟩

theorem ys10_of_cat_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → S11CatInputs G) : YS10 :=
  ys10_of_inputs fun G _ _ m hctx => (hin G m hctx).toS11Inputs hctx

end CFSG.LocalAnalysis.GLTheoremA
