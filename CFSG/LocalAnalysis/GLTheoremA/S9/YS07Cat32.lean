module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat29
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM10Main
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TablesHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I107Res6 : Prop where
  out : OutRank107
  lowExcRest2 : I107X.TwoRankLowExcRest2
  even : CoverEvenAt

section Ys07Cat32


theorem ys07_of_cat32_inputs
    (hI : KD264Lie.KD264LieInputs) (hI5 : I107Res6)
    (hR : I264bResidual2) (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (h137 : I137Res2)
    (hPar : I141F.ParityModel) (h2610 : I2610Res) : YS07 :=
  ys07_of_cat29_inputs (KD264Lie.kd264KLie_holds hI)
      ⟨rk2Tables_holds.inn, hI5.out, hI5.lowExcRest2, hI5.even⟩ hR
      ⟨hChev, I1429Residual_of_I1429OuterInner hOI⟩ h137 hPar h2610

end Ys07Cat32

end CFSG.LocalAnalysis.GLTheoremA
