module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat12
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Reduce

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure S8Cat13Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  i1017 : I1017At G p
  i1016Row : I1016RowAt G p
  i301A : I301AAt G p
  in84_i1430 : S8.L84.I1430At G
  in84_i1431 : S8.L84.I1431At G
  in8910_i301B : S8.L89.I301BAt G p
  in8910_i1420 : S8.L89.I1420CfgAt G p
  in8910_i1431 : S8.L89.I1431At G
  in8910_i1432 : S8.L89.I1432At G

section Ys06Cat13


theorem S8Cat13Inputs.toS8Cat12Inputs
    (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6) {G : Type} [Group G]
    [Finite G] {p : ℕ} (h : S8Cat13Inputs G p) : S8Cat12Inputs G p where
  i1017 := h.i1017
  i1016Row := h.i1016Row
  i301A := h.i301A
  in84_i1430 := h.in84_i1430
  in84_i1431 := h.in84_i1431
  in8910_i301B := h.in8910_i301B
  in8910_i1420 := h.in8910_i1420
  in8910_i1431 := h.in8910_i1431
  in8910_i2016 := I2016.I2016_of_facts (G := G) hSp hU6
  in8910_i1432 := h.in8910_i1432

theorem ys06_of_cat13_inputs
    (hS : YS06SporTables2NoNine) (hI : Timm.UnitaryPoint.UnitaryPointIdentification)
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat13Inputs G p) : YS06 :=
  ys06_of_cat12_inputs hS hI hE27 hSp48 fun G _ _ m hctx p hp => (hin G m hctx p hp).toS8Cat12Inputs hSp hU6

end Ys06Cat13

end CFSG.LocalAnalysis.GLTheoremA
