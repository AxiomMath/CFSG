module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat32
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137F5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I137Res3 : Prop where
  chev : I137ChevClosureComp
  l3 : I137LieCore3

section Ys07Cat33


theorem ys07_of_cat33_inputs
    (hI : KD264Lie.KD264LieInputs) (hI5 : I107Res6)
    (hR : I264bResidual2) (hChev : I1431ChevTwoS) (hOI : I1429OuterInner) (h137 : I137Res3)
    (hPar : I141F.ParityModel) (h2610 : I2610Res) : YS07 :=
  ys07_of_cat32_inputs hI hI5 hR hChev hOI ⟨h137.chev, i137Order5_holds, h137.l3⟩ hPar h2610

end Ys07Cat33

end CFSG.LocalAnalysis.GLTheoremA

end
