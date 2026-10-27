module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat31
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Holds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResSchur
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430ChevHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1430Res3 : Prop where
  cls : S8.L84.I1430Cls
  suz : S8.L84.I1430M23Suz
  on : S8.L84.I1430M23ON

section Ys06Ofcat34Inputs


theorem ys06_of_cat34_inputs
    (hE27 : S8.L84.I106TE27Fact) (hFpf : I2016Sp.FpfIrrGap) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res3) (hYD4 : I1431Y.I1431YD4Two) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact)
    (h20 : I1420Res) (h32 : I1432Res2) (h31 : I1431cRes5)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat31_inputs hE27 (I2016Sp.i2016FactSp_of_gaps HSubT.schurSp8_holds hFpf) hU6
      ⟨h30.cls, h30.suz, h30.on, S8.L84.i1430M23Chev_holds⟩ ⟨hYD4, I1431Y.i1431YU4Eight_holds⟩ hM3
      hM5 h20 h32 h31 hin

end Ys06Ofcat34Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
