module

public import CFSG.LocalAnalysis.GLTheoremA.S10.YS09Cat15
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRResAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys09Cat16


theorem ys09_of_cat16_inputs
    (hD : D4XF.D4TwoAutNormInn) (h264 : KD264Res)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S10Cat15Inputs G p) : YS09 :=
  ys09_of_cat15_inputs hD ys09FRTables_holds h264 hin

end Ys09Cat16

end CFSG.LocalAnalysis.GLTheoremA
