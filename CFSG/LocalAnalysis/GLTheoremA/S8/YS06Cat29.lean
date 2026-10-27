module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat27
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TSp48
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430AltHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1430Res2 : Prop where
  cls : S8.L84.I1430Cls
  suz : S8.L84.I1430M23Suz
  on : S8.L84.I1430M23ON
  chev : S8.L84.I1430M23Chev

section Ys06Ofcat29Inputs


theorem ys06_of_cat29_inputs
    (hE27 : S8.L84.I106TE27Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res2) (hY : I1431YRes2) (hChev : I1431ChevTwoS) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact)
    (h20 : I1420Res) (h32 : I1432Res2) (h31 : I1431cRes4)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat27_inputs hE27 S8.L84.i106TSp48Fact_holds hSp hU6
      ⟨h30.cls, S8.L84.i1430M23Alt_holds, h30.suz, h30.on, h30.chev⟩ hY hChev hM3 hM5 h20 h32 h31
      hin

end Ys06Ofcat29Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
