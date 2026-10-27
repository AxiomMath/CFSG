module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat15
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4OutHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

section Ys07Cat16


theorem ys07_of_cat16_inputs
    (h264 : KD264Res) (hInn : CatB.U4InnRest)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat15Inputs G p) : YS07 :=
  ys07_of_cat15_inputs h264 ⟨hInn, CatB.u4OutRest_holds⟩ hin

end Ys07Cat16

end CFSG.LocalAnalysis.GLTheoremA
