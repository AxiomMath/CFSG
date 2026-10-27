module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat35
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432WitTD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1432Res4 : Prop where
  d4 : H1420.I1432ClsD4
  g2 : H1420.I1432ClsG2
  td4 : H1420.TD4Res
  bd4 : H1420.I1432BD4

section Ys06Ofcat36Inputs


theorem ys06_of_cat36_inputs
    (hE27 : S8.L84.I106TE27Fact) (hFpf : I2016Sp.FpfIrrGap) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res3) (hYD4 : I1431Y.I1431YD4Two) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact)
    (h20 : I1420Res) (h32 : I1432Res4) (hG2c : H1420.WitG2.G2CommRes) (hG2d : H1420.WitG2.G2DirectRes)
    (h31 : I1431cRes5)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat35_inputs hE27 hFpf hU6 h30 hYD4 hM3 hM5 h20 ⟨h32.d4, h32.g2, H1420.i1432WitD4_holds,
    H1420.i1432WitG2_of_residuals hG2c hG2d h32.td4, h32.bd4⟩ h31 hin

end Ys06Ofcat36Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
