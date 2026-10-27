module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.S8.I2014HN

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S6Cat7Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
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
  i2017 : I2017At G
  i264ChevTwo : I264ChevTwoAt G p

section Ys05Cat7


theorem S6Cat7Inputs.toS6Cat6Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S6Cat7Inputs G p) : S6Cat6Inputs G p :=
  ⟨h.i1416, h.i71i117, h.i196, h.i2019, h.i248, h.i267, h.i268, h.i81, h.i2020, h.i1415, h.i1415Nine,
    h.i1415Seven, h.i1422, S8.HNRows.i2014At_holds G, h.i2017, h.i264ChevTwo⟩

theorem ys05_of_cat7_inputs
    (h : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
      ∀ p ∈ Mu G m, S6Cat7Inputs G p) : YS05 :=
  ys05_of_cat6_inputs_proved fun G _ _ m hctx p hp => (h G m hctx p hp).toS6Cat6Inputs

end Ys05Cat7

end CFSG.LocalAnalysis.GLTheoremA
