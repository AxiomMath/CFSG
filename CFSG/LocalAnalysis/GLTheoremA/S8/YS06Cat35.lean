module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat34
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432Cent

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1432Res3 : Prop where
  d4 : H1420.I1432ClsD4
  g2 : H1420.I1432ClsG2
  wd4 : H1420.I1432WitD4
  wg2 : H1420.I1432WitG2
  bd4 : H1420.I1432BD4

section Ys06Ofcat35Inputs


theorem ys06_of_cat35_inputs
    (hE27 : S8.L84.I106TE27Fact) (hFpf : I2016Sp.FpfIrrGap) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res3) (hYD4 : I1431Y.I1431YD4Two) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact)
    (h20 : I1420Res) (h32 : I1432Res3) (h31 : I1431cRes5)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat34_inputs hE27 hFpf hU6 h30 hYD4 hM3 hM5 h20 ⟨h32.d4, h32.g2, h32.wd4, h32.wg2, H1420.i1432Cent_holds,
    h32.bd4⟩ h31 hin

end Ys06Ofcat35Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
