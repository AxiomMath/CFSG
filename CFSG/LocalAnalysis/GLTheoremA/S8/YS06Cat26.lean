module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat22
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429Inner
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I1431cRes4 : Prop where
  lie : H1431c.I1431LieS
  alt : H1431c.I1431AltS
  f4 : H1431c.I1431InspF42
  sp68 : H1431c.I1431InspSp68
  sp492 : H1431c.I1431InspSp492
  mult : H1431c.I1431MultS

section Ys06Ofcat26Inputs

theorem ys06_of_cat26_inputs
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp)
    (hU6 : I2016.I2016FactU6) (h30 : I1430Res) (hY : I1431YRes) (hChev : I1431ChevTwoS) (hM3 : H1017.I1016M3Fact)
    (hM5 : H1017.I1016M5Fact) (h20 : I1420Res) (h32 : I1432Res2) (h31 : I1431cRes4)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  ys06_of_cat20_inputs ⟨ys06SporTables2NoNine_holds.base.bm, ys06SporTables2NoNine_holds.cfgI⟩ hE27
      hSp48 hSp hU6 h30 hY hChev ⟨i1429SubfieldOut_holds, i1429InnerRest_holds⟩
      (H1017.i1016RowFacts_of_named H1017.i1016LyFact_holds H1017.i1016Co2Fact_holds
          H1017.i1016Co1Fact_holds H1017.i1016Fi24Fact_holds H1017.i1016SuzFact_holds
          H1017.i1016ThFact_holds hM3 hM5) h20
      ⟨h32.d4, h32.g2, h32.wd4, h32.wg2, H1420.WitFi24.i1432WitFi24_holds, h32.cent, h32.bd4⟩
      ⟨h31.lie, h31.alt, H1431c.i1431SporS_holds, h31.f4, h31.sp68, h31.sp492, h31.mult⟩ hin

end Ys06Ofcat26Inputs

end CFSG.LocalAnalysis.GLTheoremA

end
