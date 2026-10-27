module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.BetaBase
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

variable [D2Amb3 G]

theorem D2L34BetaConf3.exists_base_of_cover (hFF : CitedFFL34BestOffender)
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) :
    ∃ U : Subgroup G, IsBetaBase H M U ∧ IsSylowTwoOf U (GLBPrimeCore 3 (H ⊓ M)) ∧
      A ≤ Subgroup.normalizer (U : Set G) ∧ Subgroup.normalizer (U : Set G) ≤ H ∧
      IsSylowTwoOf (U ⊓ GLBPrimeCore 3 M) (GLBPrimeCore 3 M) := by
  obtain ⟨V, hV, hAV⟩ := D2L34BetaConf3.exists_isSylowTwoOf_glbPrimeCore_inf hc
  obtain ⟨C, hCV, hC1, hchar, hcovC⟩ := D2L34BetaConf3.exists_char_cover hFF hc hstr hV hAV
  have hNV : Subgroup.normalizer (V : Set G) ≤ H :=
    D2L34BetaConf3.normalizer_le_of_char_cover hc hstr hOnly hV.2.1 hAV hCV hC1 hchar hcovC
  exact ⟨V, D2L34BetaConf3.isBetaBase_of_isSylowTwoOf hc hV, hV, hAV, hNV,
    D2L34BetaConf3.isSylowTwoOf_inf_glbPrimeCore_of_normalizer_le hc hV hAV hNV⟩

theorem D2L34BetaConf3.isSylowTwoOf_of_cover (hFF : CitedFFL34BestOffender)
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hstr : GLBStronglyEmbedded 3 M)
    (hOnly : D2OnlyL34At P M) {T : Subgroup G} (hT : IsSylowTwoOf T (H ⊓ M)) :
    IsSylowTwoOf T M ∧ Subgroup.normalizer (T : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hCT, hC1, hchar, hcovC⟩ := D2L34BetaConf3.exists_char_cover_syl hFF hc hstr hT
  have hNT := D2L34BetaConf3.normalizer_le_of_char_cover' hc hstr hOnly hT.2.1 hCT hC1 hchar
    hcovC
  refine ⟨?_, hNT⟩
  have hTM : T ≤ M := hT.1.trans inf_le_right
  obtain ⟨S, hTS, hS⟩ := exists_isSylowTwoOf_of_le hTM hT.2.1
  have hST : S ≤ T := by
    refine CFSG.AGLEmbeddingD2.le_of_normalizer_inf_le hS.2.1 ?_
    rw [inf_of_le_right hTS]
    have hle : S ⊓ Subgroup.normalizer (T : Set G) ≤ H ⊓ M :=
      le_inf (inf_le_right.trans hNT) (inf_le_left.trans hS.1)
    exact (hT.eq_of_le (le_inf hTS Subgroup.le_normalizer) hle (hS.2.1.to_le inf_le_left)).le
  rwa [le_antisymm hST hTS] at hS

end CFSG.LocalAnalysis.RankThreeTheoremC
