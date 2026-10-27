module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat40
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Proved
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420ModelEq

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1420Res2 : Prop where
  ly : H1420.I1420Ly
  co1 : H1420.I1420Co1
  suz : H1420.I1420Suz
  suzh : H1420.I1420Suzh

section Ys06Ofcat41Inputs


theorem ys06_of_cat41_inputs
    (hFpf : I2016Sp.FpfIrrGap) (hU6 : I2016.I2016FactU6) (hCls : S8.L84.I1430Cls)
    (hYD4 : I1431Y.I1431YD4Two) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact) (h20 : I1420Res2)
    (h32 : I1432Res5) (h31 : I1431cRes5) (h1017 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I1017At G p)
    (h301A : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), I301AAt G p)
    (h301B : ∀ (G : Type) [Group G] [Finite G] (p : ℕ), S8.L89.I301BAt G p) : YS06 :=
  ys06_of_cat40_inputs hFpf hU6 hCls hYD4 hM3 hM5 ⟨h20.ly, h20.co1, h20.suz, h20.suzh, H1420.i1420M3_of_i1420M3A
    H1420.i1420M3A_proved, H1420.i1420M5_of_i1420M5A H1420.i1420M5A_proved⟩ h32 h31 h1017 h301A h301B

end Ys06Ofcat41Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
