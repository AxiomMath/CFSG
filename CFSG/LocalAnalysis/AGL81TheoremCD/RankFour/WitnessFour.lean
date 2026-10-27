module

public import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

variable {G : Type} [Group G] [Finite G]

theorem Standing4.toGen (hS : Standing4 G) : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G where
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  charTwo := hS.charTwo
  rank := le_trans (by norm_num) hS.rank

theorem noXBlockFor_of_inputsK (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (hS : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G) :
    CFSG.AGLEmbeddingD2.NoXBlockFor G := by
  intro M Y hM hYM hsub hY
  have hrank : 3 ≤ CFSG.Assembly.evenRank G :=
    (CFSG.AGLEmbedding.NoXBlock.open_evenRank_eq (G := G)) ▸ hS.rank
  have hle := CFSG.AGLEmbedding.NoXBlock.evenRank_le_two_of_inOmegaK h1 h2 h25
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hS.kProper)
    hS.simple (CFSG.AGLEmbedding.NoXBlock.assembly_isCharTwoType_of_open hS.charTwo)
    ⟨CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY, M,
      CFSG.AGLEmbedding.NoXBlock.isMaximalTwoLocal_of_glb hM, hYM,
      CFSG.AGLEmbedding.NoXBlock.isSubnormal_subgroupOf_of_open hsub⟩
  omega

@[expose] def witnessFour (G : Type) [Group G] [Finite G] :
    ∀ p : ℕ, Sylow p G → Subgroup G → Prop :=
  fun p P M => uniqueFourIsMaxTwoLocal M ∧ p ∈ uniqueFourSigma M ∧ IsWitnessPrime p P ∧
    IsWitnessGen p P M

theorem witnessFour_spec :
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), witnessFour G p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M :=
  fun _ _ _ h => ⟨h.2.2.1, h.2.2.2⟩

theorem exists_witnessFour (hU : uniqueFourUnique G) {p : ℕ} {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) (hp : p ∈ uniqueFourSigma M) :
    ∃ P : Sylow p G, witnessFour G p P M := by
  obtain ⟨hpβ, hMne, -, P, hPN, hΓ, hcase⟩ := (hU M hM ⟨p, hp⟩).1 p hp
  refine ⟨P, hM, hp, ⟨hpβ.1, hpβ.2.1, ?_⟩, ⟨hM, ?_, ?_, ?_⟩⟩
  · exact le_trans (by norm_num) (four_le_pRank_sylow hpβ P)
  · simpa [rankThreeGamma, uniqueFourGamma] using hΓ
  · rcases hcase with ⟨hdvd, hstrong⟩ | ⟨h5, hsolv, -, P₀, hP₀⟩
    · haveI : Fact p.Prime := ⟨hpβ.1⟩
      have hPne : (P : Subgroup G) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := G) (p := p) P hpβ.2.2.1
      have hstr :=
        CFSG.LocalAnalysis.UniquenessCase.UC6.isStronglyPEmbedded_of_clause_one
          hMne hdvd hstrong
      exact Or.inl (by
        rw [CFSG.LocalAnalysis.RankThreeUC.gamma_one_le_iff_isStronglyPEmbedded hPN hMne hPne]
        exact hstr)
    · exact Or.inr (Or.inl ⟨h5, hsolv⟩)
  · intro H hH h2
    exact (hU M hM ⟨p, hp⟩).2 H hH ⟨p, hp, h2⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
