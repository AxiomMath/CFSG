module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat13
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TimmUnitaryPoint

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys06Cat14


theorem ys06_of_cat14_inputs
    (hS : YS06SporTables2NoNine)
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat13Inputs G p) : YS06 :=
  ys06_of_cat13_inputs hS Timm.UnitaryPoint.unitaryPointIdentification hE27 hSp48 hSp hU6 hin

end Ys06Cat14

end CFSG.LocalAnalysis.GLTheoremA
