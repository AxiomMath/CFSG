module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat18
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06K15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5InspL2
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat14
public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat17

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys06Cat19


theorem ys06_of_cat19_inputs
    (hS : YS06SporTables2NoNine)
    (hE27 : S8.L84.I106TE27Fact) (hSp48 : S8.L84.I106TSp48Fact) (hSp : I2016.I2016FactSp) (hU6 : I2016.I2016FactU6)
    (h30 : I1430Res) (hY : I1431YRes) (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (hRow : H1017.I1016RowFacts)
    (h20 : I1420Res) (h32 : I1432Res) (h31 : I1431cRes2)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S8Cat17Inputs G p) : YS06 :=
  have hI3 : I1431Res3 := ⟨hChev, I1429Residual_of_I1429OuterInner hOI⟩
  have h31' : I1431cRes :=
    ⟨h31.lie, h31.alt, h31.spor, h31.f4, h31.sp68, h31.sp492, H1431c.I1431InspL2_holds, h31.hn, h31.mult⟩
  ys06_of_cat14_inputs hS hE27 hSp48 hSp hU6 fun G _ _ m hctx p hp =>
    ((((hin G m hctx p hp).toS8Cat16Inputs h20 h32 h31' hctx.1.simple hctx.1.kProper).toS8Cat15Inputs hRow).toS8Cat13InputsK
      h30 hY hI3)

end Ys06Cat19

end CFSG.LocalAnalysis.GLTheoremA

end
