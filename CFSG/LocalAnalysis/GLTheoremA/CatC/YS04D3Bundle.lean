module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D3Fin

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure D3Facts : Prop where
  cent : D3TrialityCentRank
  inner : D3InnerInvolution
  field : D3FieldInvolution
  fpf : D3FixedPointFree

section D3Bundle


theorem ys04_of_d3Facts
    (h : D3Facts) : YS04 :=
  ys04_of_facts h.cent h.inner h.field h.fpf

theorem noTrialityCharThreeAt_of_d3Facts
    (h : D3Facts) {G : Type} [Group G] [Finite G] {m : ℕ}
    (hctx : ThmACtx G m) : NoTrialityCharThreeAt G :=
  noTrialityCharThreeAt_of_facts hctx h.cent h.inner h.field h.fpf

end D3Bundle

end CFSG.LocalAnalysis.GLTheoremA
