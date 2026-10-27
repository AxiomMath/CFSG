module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat19
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LRest
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bRes2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

structure I107Res3 : Prop where
  inn : Rk2InnRank
  out : OutRank107
  lowExc : I107L.TwoRankLowExc
  even : CoverEvenAt

section Ys07Cat20


theorem ys07_of_cat20_inputs
    (h264 : KD264Res) (hInn : CatB.U4InnRest) (hI : I107Res3) (hR : I264bResidual2)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat19Inputs G p) : YS07 :=
  ys07_of_cat19_inputs h264 hInn ⟨hI.inn, hI.out, I107L.twoRankLowRest_of_exc hI.lowExc, hI.even⟩
    (i264bResidual_of_2 hR) hin

end Ys07Cat20

end CFSG.LocalAnalysis.GLTheoremA
