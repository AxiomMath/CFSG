module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WKmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.EscapeCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34BetaConf3.isSylowTwoOf_of_cover_of_nine (hFF : CitedFFL34BestOffender)
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M) (hOnly : D2OnlyL34At P M) {T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) :
    IsSylowTwoOf T M ∧ Subgroup.normalizer (T : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C, hCT, hC1, hchar, hcovC⟩ := D2L34BetaConf3.exists_char_cover_syl_of_nine hFF hc hR9 hT
  have hNT := D2L34BetaConf3.normalizer_le_of_char_cover_of_nine' hc hR9 hrk hOnly hT.2.1 hCT hC1
    hchar hcovC
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


theorem D2L34BetaConf3.not_normalizer_le_of_isSylowTwoOf_of_nine
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M) (hOnly : D2OnlyL34At P M) {T : Subgroup G}
    (hT : IsSylowTwoOf T (H ⊓ M)) :
    ¬ Subgroup.normalizer (T : Set G) ≤ M := by
  intro hNM
  have hAH : A ≤ H := hc.esc.A_le.trans hc.esc.le_H
  have hAM : A ≤ M := hc.esc.A_le.trans hc.esc.le_M
  have hcov := D2L34BetaConf3.cover_of_isSylowTwoOf_of_nine hc hR9 hT (B := A) (Y := H ⊓ M)
    (le_inf hAH hAM) (IsPGroup.of_card (n := 2) hc.esc.card_A) (by simpa using hc.esc.card_A)
    hT.1 (le_inf hAH hAM) (inf_le_inf_left H hNM)
  have hN : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := hc.normalizer_eq
  have hEq := D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover_of_nine hc hR9 hrk hOnly
    (C := pCoreOf 2 (H ⊓ M))
    (fun k hk => by
      obtain ⟨a, ha, haH, e⟩ := hcov k hk
      exact ⟨a, Subgroup.mem_inf.2 ⟨haH, hN.symm ▸ ha⟩, haH, e⟩)
    hc.esc.maxTwoLocal_M (hN.le.trans inf_le_right)
  exact hc.esc.not_le (hEq ▸ le_rfl)

end CFSG.LocalAnalysis.RankThreeTheoremC
