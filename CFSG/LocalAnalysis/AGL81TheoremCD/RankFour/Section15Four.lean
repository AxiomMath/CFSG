module

public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.TheoremDFour
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.CStarGenFour

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81S15FalseFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → CFSG.Open.uniqueFourUnique G →
    ∀ (M T : Subgroup G) (T₁ T₂ : Subgroup ↥M), Section15.S15CtxGen G M T T₁ T₂ → False

theorem agl81Section15Four_of_false
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hGN : CFSG.LocalAnalysis.RankThreeUC.S15.S15GNInput)
    (hF : AGL81S15FalseFour) :
    AGL81Section15Four := by
  intro G _ _ hS4 hU p P M hw hno T hT H1 H2 H3 H4 hcon H6 H7 H8 H9 H10
  by_contra hN
  have hC : CStarGen G := cStarGen_of_unique4 hS4 hU
  have hX : CFSG.AGLEmbeddingD2.NoXBlockFor G :=
    noXBlockFor_of_inputsK h1 h2 h25 (Standing4.toGen hS4)
  have hpσ : p ∈ rankThreeSigmaA G := by
    rw [sigmaA_eq_uniqueFourBeta hS4]
    exact hw.2.1.1
  have hspec : IsWitnessPrime p P ∧ IsWitnessGen p P M := witnessFour_spec p P M hw
  have hwit : ∀ q ∈ sigmaSet G M,
      ∃ Q : Sylow q G, IsWitnessPrime q Q ∧ IsWitnessGen q Q M := by
    intro q hq
    rw [sigmaM_eq_uniqueFourSigma hS4 hU hw.1] at hq
    obtain ⟨Q, hQ⟩ := exists_witnessFour hU hw.1 hq
    exact ⟨Q, witnessFour_spec q Q M hQ⟩
  have hnoAll : ∀ q ∈ sigmaSet G M, ¬ U4Shape q M := by
    intro q hq
    rw [sigmaM_eq_uniqueFourSigma hS4 hU hw.1] at hq
    exact not_u4Shape_of_mem_uniqueFourSigma hq
  obtain ⟨T₁, T₂, hctx⟩ :=
    Section15.S15CtxGen.of_hyps hC hX hGN hpσ hspec.1 hspec.2 hwit hnoAll hT H2 H3 hcon hN
  exact hF G hS4 hU M T T₁ T₂ hctx

theorem agl81TheoremDFour_of_false
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hHup : CFSG.LocalAnalysis.RankThreeUC.KFactHuppertProductThree)
    (hI59 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.AGL81I59)
    (hGN : CFSG.LocalAnalysis.RankThreeUC.S15.S15GNInput)
    (hF : AGL81S15FalseFour) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour :=
  agl81TheoremDFour_of_section15Four h1 h2 h25 hHup hI59
    (agl81Section15Four_of_false h1 h2 h25 hGN hF)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
