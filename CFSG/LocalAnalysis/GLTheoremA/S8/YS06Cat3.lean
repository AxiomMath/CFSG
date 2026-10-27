module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat2
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1016Fi22
public import CFSG.LocalAnalysis.GLTheoremA.S8.I1423HN

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Timmesfeld.Coordinator

structure S8Cat3Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i66 : I66At
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  timmesfeld : TimmesfeldAt
  no5Pumpup : No5PumpupAt
  in83_i1016HN : S8.L83.I1016HNAt G
  in83_i112 : S8.L83.I112SingleAt G
  in83_i1415 : S8.L83.I1415NineAt G
  in83_i2014 : S8.L83.I2014UsedAt G
  in84_i1430 : S8.L84.I1430At G
  in84_i106 : S8.L84.I106T1430At G
  in84_i1431 : S8.L84.I1431At G
  in84_kfacts : S8.L84.KFactsAt G
  in8910_cfgI : S8.L89.CfgIAt G p
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1431 : S8.L89.I1431At G
  in8910_i2016 : S8.L89.I2016At G
  in8910_i1432 : S8.L89.I1432At G


variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem S8Cat3Inputs.toS8Cat2Inputs
    (h : S8Cat3Inputs G p) : S8Cat2Inputs G p :=
  ⟨h.i66, h.i1017, h.i1016Row, h.i301A, h.timmesfeld, h.no5Pumpup, S8.CoRows.i1016Co2At_holds G,
    ⟨h.in83_i1016HN, S8.CoRows.i1016Co1At_holds G, S8.HNRows.i1423At_holds G, h.in83_i112,
      h.in83_i1415, h.in83_i2014⟩,
    ⟨S8.L84.i1016ONAt_holds G, S8.L84.i1425At_holds G, h.in84_i1430, h.in84_i106, h.in84_i1431,
      h.in84_kfacts, S8.L84.onFactsAt_holds G⟩,
    ⟨h.in8910_cfgI, h.in8910_i301B, h.in8910_i1420, S8.CoRows.i1016At89_holds G, h.in8910_i1431,
      h.in8910_i2016, h.in8910_i1432⟩⟩

theorem ys06_of_cat3_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S8Cat3Inputs G p) : YS06 :=
  ys06_of_cat2_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat2Inputs

end CFSG.LocalAnalysis.GLTheoremA
