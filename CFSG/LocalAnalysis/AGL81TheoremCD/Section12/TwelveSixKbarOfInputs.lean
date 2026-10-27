module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixOfCtx
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
public import CFSG.CGT.Foote82.T66.Proof511One
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarType
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNineTenOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKInter
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarExclusion
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarThompson
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIMemberHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeM
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNEqOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BlockOrderThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.NineTen
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.CGT6.Emb5NinePair
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]


theorem twelveSixKbar_of_inputs {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (hsyl : CFSG.ABGLocalTools.IsSylowOf p Q H)
    (h812 : Section15.O812sixGen) (h124 : TwelveFour M H)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L))
    (hdvdL : ∀ q : ℕ, q ∈ sigmaSet G M → ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      q ∣ Nat.card L)
    (hcard : (weakBlockSet M H).ncard = 3)
    (hk1 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      CFSG.Open.pRank 3 (CFSG.AGLEmbedding.barM M L) ≤ 1)
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hI : NineNineOneInput) (h10 : NineTenGen) (h912 : NineTwelveKerConclusion G M Q H Q p)
    (hCov : CFSG.CGT.Foote82.Proof511.PSp43Cover)
    (hS : TwelveSixKbarSingle) (hList : TwelveSixKbarList)
    {d : ℕ} {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}
    (hd : TwelveFiveData M H d L₁ L₂ L₃ n₁ n₂ n₃) :
    TwelveSixKbar M H p n₁ n₂ n₃ := by
  have hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ :=
    { ctx := h
      data := hd
      hcard := hcard
      h3 := pRank_three_le_three_of_twelveCtx h h124
      hm3 := fun L hL =>
        le_antisymm (hk1 L hL) (one_le_pRank_three_barM h1 h2 h25 h hL)
      hC := fun L W hL hW hWL =>
        centralizer_le_of_mem_weakBlockSet h h812 hd.mem_sigma hL3
          (hdvdL d hd.mem_sigma) hcard.ge hL hW hWL
      hI := hI
      h910 := fun E hEQ hE hEc hΓ =>
        nineTenConclusion_of_twelveCtx (E := E) h10 h hEQ hE hEc hΓ
      h912 := h912 }
  have hIM : TwelveSixIMember := twelveSixIMember_of_K h1 h2 h25
  obtain ⟨D⟩ := hc.exists_iData hIM
  have hA : ¬ pLayerIn p H ≤ M := hc.not_pLayerIn_le hIM
  obtain ⟨hXM, -, hKH⟩ := hc.nineTenOne_i D hA
  obtain ⟨hp, hK, hty⟩ :=
    hc.kbar_type D hsyl hA hS hList twelveSixKbarExclusion_holds hCov
  obtain ⟨hn₁, hn₂, hn₃⟩ := hc.n_eq_one_of_kbarType D hXM hKH hK hty
  refine ⟨hn₁, hn₂, hn₃, hp, hty, ?_⟩
  exact hc.k_inter D hp hXM hKH hK hty kFactKbarThompsonNormalizer_holds

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
