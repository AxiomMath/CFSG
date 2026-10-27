module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat29
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cMult

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1431cRes5 : Prop where
  lie : H1431c.I1431LieS
  alt : H1431c.I1431AltS
  f4 : H1431c.I1431InspF42
  sp68 : H1431c.I1431InspSp68
  sp492 : H1431c.I1431InspSp492

section Ys06Ofcat31Inputs


theorem ys06_of_cat31_inputs
    (hE27 : S8.L84.I106TE27Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res2) (hY : I1431YRes2) (hM3 : H1017.I1016M3Fact) (hM5 : H1017.I1016M5Fact) (h20 : I1420Res)
    (h32 : I1432Res2) (h31 : I1431cRes5)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat29_inputs hE27 hSp hU6 h30 hY i1431ChevTwoS_holds hM3 hM5 h20 h32
      ⟨h31.lie, h31.alt, h31.f4, h31.sp68, h31.sp492, H1431c.i1431MultS_holds⟩ hin

end Ys06Ofcat31Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
