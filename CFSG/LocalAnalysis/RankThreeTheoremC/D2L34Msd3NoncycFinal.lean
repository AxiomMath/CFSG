module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycPair
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycCore
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycFactor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Baum

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem ffNoncyclicInput3_of_nodes
    (hI59 : AGL81I59) (hX : D1NoXBlock3 G) (hGS : FFGroupStep3 G) : FFNoncyclicInput3 G := by
  intro d P M A H R Rbar K ctx hstr hcon T hT hNT S hS
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMtop : M ≠ ⊤ := fun h => hc.esc.not_le (h ▸ le_top)
  have hKg : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
        (D2Amb3.glob (G := G)).kProper) M hMtop
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  have hT1 : T ≠ ⊥ := by
    intro h
    apply twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  set Z := quasithinOmegaOneCenter T with hZdef
  set V := CFSG.Quasithin.conjClosure Z M with hVdef
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := CFSG.Quasithin.le_normalizer_conjClosure Z M
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  ·
    have hZ1 : Z ≠ ⊥ := Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1
    have hZ2 : IsPGroup 2 Z := hT.2.1.to_le (Setup.omegaOneCenterOf_le T)
    have hJ1 : thompsonJ T ≠ ⊥ := Setup.thompsonJ_ne_bot hT.2.1 hT1
    have hJ2 : IsPGroup 2 (thompsonJ T) := hT.2.1.to_le (B6.thompsonJ_le T)
    obtain ⟨-, hfac⟩ := CFSG.Quasithin.B2_7_of_le_factor hMV hT hJ
    have hfac' : ∀ m ∈ M, ∃ c ∈ ffC M T, ∃ b ∈ M ⊓ Subgroup.normalizer (thompsonJ T : Set G),
        m = c * b := by
      intro m hm
      obtain ⟨n, hn, c, hc', he⟩ := hfac m⁻¹ (M.inv_mem hm)
      refine ⟨c⁻¹, ?_, n⁻¹, (M ⊓ Subgroup.normalizer (thompsonJ T : Set G)).inv_mem hn, ?_⟩
      · have := (M ⊓ Subgroup.centralizer (V : Set G)).inv_mem hc'
        show c⁻¹ ∈ Subgroup.centralizer (V : Set G) ⊓ M
        rwa [inf_comm] at this
      · rw [← mul_inv_rev, ← he, inv_inv]
    have hCZ : ffC M T ≤ Subgroup.normalizer (Z : Set G) :=
      (Subgroup.centralizer_le (CFSG.Quasithin.le_conjClosure Z M)).trans
        (Subgroup.centralizer_le_normalizer _) |> fun h => inf_le_left.trans h
    exact exists_normal_order_three_of_factorization3 ctx hstr hcon hT hNT S hS hZ1 hZ2 hJ1 hJ2
      (CFSG.AGLEmbeddingD2.Tits.MsidePrelim.normalizer_le_normalizer_quasithinOmegaOneCenter T)
      (GammaExtra.normalizer_le_normalizer_thompsonJ T) hCZ inf_le_left inf_le_right hfac'
  ·
    have hconAut := ffQuotientConstrained3 hc hstr hcon hT hNT S hS
    have hFF : FFConclusion M T V := hI59 G M T V hKg hF hT rfl hconAut hJ
    obtain ⟨hU, hMN, I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFF
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3 hN hGS ctx hstr hcon hT hNT hU I hMN hcard hJM
      hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU (baum T) ≤ autI hU (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU (hT.2.1.to_le (C1GN.baum_le T)))
    obtain ⟨B, hBM, hBN, hfac⟩ := exists_factorization_of_pairData3 hc hstr hT hNT hMN hI hcard
      hSylB hJM hdat (D := (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)
      (Subgroup.map_subtype_le _) (S.isPGroup'.map _) hS
    obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, hCM₁, -, -⟩ := hdat
    exact exists_normal_order_three_of_factorization3 ctx hstr hcon hT hNT S hS hC₁1 hC₁2 hC₂1
      hC₂2 hT₁ hT₂ hCM₁ hBM hBN hfac

end CFSG.LocalAnalysis.RankThreeTheoremC
