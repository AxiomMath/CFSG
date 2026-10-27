module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat4
public import CFSG.LocalAnalysis.GLTheoremA.S8.I112SingleHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S8Cat5Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i66 : I66At
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  timmesfeld : TimmesfeldAt
  no5Pumpup : No5PumpupAt
  in83_i1415 : S8.L83.I1415NineAt G
  in84_i1430 : S8.L84.I1430At G
  in84_i106 : S8.L84.I106T1430At G
  in84_i1431 : S8.L84.I1431At G
  in8910_cfgI : S8.L89.CfgIAt G p
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1431 : S8.L89.I1431At G
  in8910_i2016 : S8.L89.I2016At G
  in8910_i1432 : S8.L89.I1432At G

section Ys06Cat5


theorem S8Cat5Inputs.toS8Cat4Inputs
    {G : Type} [Group G] [Finite G] {p : ℕ}
    (h : S8Cat5Inputs G p) : S8Cat4Inputs G p where
  i66 := h.i66
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  timmesfeld := h.timmesfeld
  no5Pumpup := h.no5Pumpup
  in83_i112 := S8.L83.i112SingleAt_holds G
  in83_i1415 := h.in83_i1415
  in84_i1430 := h.in84_i1430
  in84_i106 := h.in84_i106
  in84_i1431 := h.in84_i1431
  in8910_cfgI := h.in8910_cfgI
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := h.in8910_i1431
  in8910_i2016 := h.in8910_i2016
  in8910_i1432 := h.in8910_i1432

theorem ys06_of_cat5_inputs
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m →
    ∀ p ∈ Mu G m, S8Cat5Inputs G p) : YS06 :=
  ys06_of_cat4_inputs fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat4Inputs

end Ys06Cat5

end CFSG.LocalAnalysis.GLTheoremA
