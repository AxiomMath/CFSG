module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat19
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cHN
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealSuz

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1431cRes3 : Prop where
  lie : H1431c.I1431LieS
  alt : H1431c.I1431AltS
  spor : H1431c.I1431SporS
  f4 : H1431c.I1431InspF42
  sp68 : H1431c.I1431InspSp68
  sp492 : H1431c.I1431InspSp492
  mult : H1431c.I1431MultS

structure YS06SporTables2NoI66 : Prop where
  bm : CFSG.HardMathSupport.Solomon.Coordinator.NoOrderSixtyFiveBM
  cfgI : CfgIRes

section Ys06Cat20


theorem ys06_of_cat20_inputs
    (hS : YS06SporTables2NoI66)
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res) (hY : I1431YRes) (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hRow : H1017.I1016RowFacts)
    (h20 : I1420Res) (h32 : I1432Res) (h31 : I1431cRes3)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat19_inputs ⟨⟨i66RealS_holds, hS.bm⟩, hS.cfgI⟩ hE27 hSp48 hSp hU6 h30 hY hChev hOI hRow h20 h32
    ⟨h31.lie, h31.alt, h31.spor, h31.f4, h31.sp68, h31.sp492, H1431c.i1431InspHN_holds, h31.mult⟩ hin

end Ys06Cat20

end CFSG.LocalAnalysis.GLTheoremA

end
