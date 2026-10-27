module

public import CFSG.LocalAnalysis.GLTheoremA.S6.YS05Cat5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05Small
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIso
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L62Core
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016CoRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S6Cat6Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1416 : I1416At G p
  i71i117 : I71I117At G p
  i196 : I196At G p
  i2019 : I2019At G p
  i248 : I248At G p
  i267 : I267At G p
  i268 : I268At G p
  i81 : I81At G p
  i2020 : I2020At G p
  i1415 : I1415At G p
  i1415Nine : I1415NineAt G
  i1415Seven : I1415SevenAt G
  i1422 : I1422At G
  i2014 : I2014At G
  i2017 : I2017At G
  i264ChevTwo : I264ChevTwoAt G p

section Ys05Cat6Fill


theorem S6Cat6Inputs.toS6Cat5Inputs {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat6Inputs G p) : S6Cat5Inputs G p :=
  ⟨h.i1416, h.i71i117, h.i196, h.i2019, h.i248, h.i267, i71U3At_holds G p, h.i268, h.i81, h.i2020,
    lieTypeNonIsoAt_holds, h.i1415, h.i1415Nine, h.i1415Seven, h.i1422, h.i2014, h.i2017,
    S8.CoRows.i1016CoAt_holds G, h.i264ChevTwo, CatB.i106L62At_holds, CatB.i131L62At_holds⟩

end Ys05Cat6Fill

section Ys05Cat6


theorem ys05_of_cat6_inputs
    (h3 : CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieComp)
    (h5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ F,
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LieCompsOn p F)
    (hLQ : ∀ p : ℕ, p.Prime → p ≠ 2 →
      CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.LieQConstrainedInner p)
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat6Inputs G p) : YS05 :=
  ys05_of_cat5_inputs h3 h5 hLQ fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat5Inputs

end Ys05Cat6

end CFSG.LocalAnalysis.GLTheoremA
