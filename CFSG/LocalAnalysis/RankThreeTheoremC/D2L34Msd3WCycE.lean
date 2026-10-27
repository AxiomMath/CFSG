module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WCycD
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WAssembly

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem ffCyclicInput3W_of_nodes
    (hX : D1NoXBlock3 G) : FFCyclicInput3W G := by
  intro d P M A H R Rbar K ctx hR9 hs T hT hNT S hS hS0
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  have hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M :=
    CFSG.ABGLocalTools.isPConstrained_of_isSolvable hs
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)
  · exact center3_of_thompson_cyclic3W ctx hR9 hT hNT S hS hJ
  · set V := conjClosure (quasithinOmegaOneCenter T) M with hV
    obtain ⟨hU, -⟩ := B2_15 hF hT
    have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
      (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
    have hsAut : Group.IsSolvable ↥(autOn M V) := by
      have := hs
      exact Group.isSolvable_of_surjective (actOnAutOn_surjective hMN)
    have hFF : FFConclusion M T V := ffConclusion_of_solvable hF hsAut hT hV hJ
    obtain ⟨hU', hMN', I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFF
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3_free hN ffGroupStep3Free ctx hT hNT hU' I hMN'
      hcard hJM hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU' (baum T) ≤ autI hU' (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN' hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU' (hT.2.1.to_le (C1GN.baum_le T)))
    exact center3_of_pairData_cyclic3W ctx hR9 hT hNT hMN' hI hcard hSylB hJM hperm rfl S hS hS0
      (ffSolvableInput G M T hF hT hcon S hS) hdat

end CFSG.LocalAnalysis.RankThreeTheoremC
