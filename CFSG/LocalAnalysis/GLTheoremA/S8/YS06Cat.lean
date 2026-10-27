module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Reduction
public import CFSG.LocalAnalysis.GLTheoremA.S8.A6Facts
public import CFSG.LocalAnalysis.GLTheoremA.S6.I2013

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator

namespace S8

structure Inputs83Cat (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1016HN : L83.I1016HNAt G
  i1016Co1 : L83.I1016Co1At G
  i1423 : L83.I1423At G
  i112 : L83.I112SingleAt G
  i1415 : L83.I1415NineAt G
  i2014 : L83.I2014UsedAt G

structure Inputs84Cat (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1016 : L84.I1016ONAt G
  i1425 : L84.I1425At G
  i183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4
  i112 : L84.I112At G
  i1430 : L84.I1430At G
  i106 : L84.I106T1430At G
  i1431 : L84.I1431At G
  kfacts : L84.KFactsAt G
  onfacts : L84.ONFactsAt G
  lbal : LBalanceAt G 3

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem Inputs83Cat.toInputs83 (h : Inputs83Cat G p) : Inputs83 G p :=
  ⟨h.i1016HN, h.i1016Co1, h.i1423, h.i112, h.i1415, i2013At_holds, h.i2014⟩

theorem Inputs84Cat.toInputs84 (h : Inputs84Cat G p) : Inputs84 G p :=
  ⟨h.i1016, h.i1425, h.i183, h.i112, L84.a6FactsAt_holds G, h.i1430, h.i106, h.i1431, h.kfacts,
    h.onfacts, h.lbal⟩

end S8

structure S8CatInputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  sporOut : SporadicOuterLeTwo
  i66 : I66At
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  timmesfeld : TimmesfeldAt
  no5Pumpup : No5PumpupAt
  i1016Co2 : I1016Co2At G
  in83 : S8.Inputs83Cat G p
  in84 : S8.Inputs84Cat G p
  in8910 : S8.Inputs8910 G p

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S8CatInputs.toS8Inputs (h : S8CatInputs G p) : S8Inputs G p :=
  ⟨h.sporOut, h.i66, h.i1017, h.i1016Row, h.i301A, h.timmesfeld, h.no5Pumpup, h.i1016Co2,
    h.in83.toInputs83, h.in84.toInputs84, h.in8910⟩

theorem ys06_of_cat_inputs (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S8CatInputs G p) : YS06 :=
  ys06_of_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Inputs

end CFSG.LocalAnalysis.GLTheoremA
