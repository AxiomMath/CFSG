module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat11
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TMain

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S8Cat12Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  in84_i1430 : S8.L84.I1430At G
  in84_i1431 : S8.L84.I1431At G
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1431 : S8.L89.I1431At G
  in8910_i2016 : S8.L89.I2016At G
  in8910_i1432 : S8.L89.I1432At G

section Ys06Cat12


theorem S8Cat12Inputs.toS8Cat10Inputs
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S8Cat12Inputs G p) : S8Cat10Inputs G p where
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  in84_i1430 := h.in84_i1430
  in84_i106 := S8.L84.I106T1430At_of_facts G hE27 hSp48
  in84_i1431 := h.in84_i1431
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := h.in8910_i1431
  in8910_i2016 := h.in8910_i2016
  in8910_i1432 := h.in8910_i1432

theorem ys06_of_cat12_inputs
    (hS : YS06SporTables2NoNine) (hI : Timm.UnitaryPoint.UnitaryPointIdentification)
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat12Inputs G p) : YS06 :=
  ys06_of_cat11_inputs hS hI fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat10Inputs hE27 hSp48

end Ys06Cat12

end CFSG.LocalAnalysis.GLTheoremA
