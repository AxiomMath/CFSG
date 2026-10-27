module

public import CFSG.LocalAnalysis.GLTheoremA.S9.YS07Cat17
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GChev
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GSurv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GLow

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def TwoRankLowRest : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (lab : GLALabel), IsSimpleGroup S → Rk2IsLabel S lab → GLAInLambda2 lab →
    ¬ exempt107 lab → lab.tag ≠ .A → twoRankLow107 lab ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S)

structure I107Res2 : Prop where
  inn : Rk2InnRank
  out : OutRank107
  low : TwoRankLowRest
  even : CoverEvenAt

section Ys07Cat18


theorem twoRankLowS_of_rest
    (h : TwoRankLowRest) : TwoRankLowS := by
  intro S _ _ lab hS hlab hL hne
  by_cases hA : lab.tag = .A
  · exact I107G.twoRankLow_tagA_holds S lab hA hS hlab
  · exact h S lab hS hlab hL hne hA

theorem ys07_of_cat18_inputs
    (h264 : KD264Res) (hInn : CatB.U4InnRest) (hI : I107Res2)
    (hin : ∀ (G : Type) [Group G] [Finite G] (m : ℕ), ThmACtx G m → ∀ p ∈ Mu G m, S9Cat17Inputs G p) : YS07 :=
  ys07_of_cat17_inputs h264 hInn
    ⟨chevTwoNonabelian_holds, hI.inn, hI.out, twoRankLowS_of_rest hI.low, hI.even, survivorLabelCat_holds⟩ hin

end Ys07Cat18

end CFSG.LocalAnalysis.GLTheoremA
