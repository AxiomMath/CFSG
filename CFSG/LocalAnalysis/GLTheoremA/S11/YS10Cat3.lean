module

public import CFSG.LocalAnalysis.GLTheoremA.S11.YS10Cat2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2Down

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S11Cat3Inputs (G : Type) [Group G] [Finite G] : Prop where
  i162 : I162At G
  i163 : I163At G
  i164 : I164At G
  i165 : I165At G
  i2315a : I2315aAt G
  i2315b : I2315bAt G
  e62 : E62At G
  i166 : I166At G
  eTable : ETableAt G
  i1441 : I1441At G
  i14neg : I14NegAt G
  i1416 : I1416Chev2At G
  i142 : I142At G
  rank3 : RankThreeLabelAt G
  u64types : U64TypesAt G
  u6struct : U6StructAt G
  u5case : U5CaseAt G

variable {G : Type} [Group G] [Finite G]

theorem S11Cat3Inputs.toS11Cat2Inputs
    (h : S11Cat3Inputs G) : S11Cat2Inputs G :=
  ⟨h.i162, h.i163, h.i164, h.i165, h.i2315a, h.i2315b, h.e62, fun p => chev2DownAt_holds p, h.i166,
    h.eTable, h.i1441, h.i14neg, h.i1416, h.i142, h.rank3, h.u64types, h.u6struct, h.u5case⟩

theorem ys10_of_cat3_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → S11Cat3Inputs G) : YS10 :=
  ys10_of_cat2_inputs fun G _ _ m hctx => (hin G m hctx).toS11Cat2Inputs

end CFSG.LocalAnalysis.GLTheoremA
