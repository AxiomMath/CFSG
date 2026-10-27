module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat26
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU5Holds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1431YRes2 : Prop where
  d4 : I1431Y.I1431YD4Two
  u4 : I1431Y.I1431YU4Eight

section Ys06Ofcat27Inputs


theorem ys06_of_cat27_inputs
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp)
    (hU6 : I2016.I2016FactU6) (h30 : I1430Res) (hY : I1431YRes2) (hChev : I1431ChevTwoS) (hM3 : H1017.I1016M3Fact)
    (hM5 : H1017.I1016M5Fact) (h20 : I1420Res) (h32 : I1432Res2) (h31 : I1431cRes4)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat26_inputs hE27 hSp48 hSp hU6 h30 ⟨hY.d4, I1431Y.i1431YU5Two_holds, hY.u4⟩ hChev hM3 hM5 h20 h32 h31
    hin

end Ys06Ofcat27Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
