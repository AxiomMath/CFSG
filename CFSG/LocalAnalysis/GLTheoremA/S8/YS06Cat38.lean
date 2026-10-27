module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat36
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys06Ofcat38Inputs


theorem ys06_of_cat38_inputs
    (hFpf : I2016Sp.FpfIrrGap) (hU6 : I2016.I2016FactU6) (h30 : I1430Res3)
    (hYD4 : I1431Y.I1431YD4Two) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact) (h20 : I1420Res)
    (h32 : I1432Res4) (hG2c : H1420.WitG2.G2CommRes) (hG2d : H1420.WitG2.G2DirectRes) (h31 : I1431cRes5)
    (h1017 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I1017At G p) (h301A : ∀ (G : Type) [Group G] [Finite G] (p :
    ℕ), I301AAt G p) (h301B : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), S8.L89.I301BAt G p)
    : YS06 :=
  ys06_of_cat36_inputs S8.L84.i106TE27Fact hFpf hU6 h30 hYD4 hM3 hM5 h20 h32 hG2c hG2d h31
      (fun G _ _ _ _ p _ => ⟨h1017 G p, h301A G p, h301B G p⟩)

end Ys06Ofcat38Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
