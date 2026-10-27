module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Z6
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27D12
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27RankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Noncyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Cyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WAssembly
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Final
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3R27Card

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G]

theorem center3_of_solvable27
    (hX : D1NoXBlock3 G) {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {T : Subgroup G}
    (c : D2L34R27 G d P M A H R Rbar K T) : Center3Conclusion M := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 ↥(ffC M T)))
  by_cases hD0 : (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype = ⊥
  · have hS0 : (S : Subgroup ↥(ffC M T)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ (S : Subgroup ↥(ffC M T)).map (ffC M T).subtype := ⟨x, hx, rfl⟩
      rw [hD0, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (Subtype.ext this)
    exact center3_of_coprime27 hX c (not_dvd_card_of_sylow_eq_bot S hS0)
  · by_cases hDc : IsCyclic ↥((S : Subgroup ↥(ffC M T)).map (ffC M T).subtype)
    · exact center3_of_cyclic27 hX c S hDc hD0
    · exact center3_of_noncyclic27 hX c S hDc

theorem d2L34BetaMSolvableR9_of_inputs
    (hX : D1NoXBlock3 G) (hIV : D2L34NonExtremalL34 G) :
    D2L34BetaMSolvableR9 G := by
  intro d P M A H R Rbar K ctx hs
  rcases ctx.conf.card_R_eq_nine_or_27 with h9 | ⟨h27, -⟩
  · exact h9
  · exfalso
    have hFF : CitedFFL34BestOffender :=
      CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.citedFFL34BestOffender
    obtain ⟨T, hT⟩ := exists_isSylowTwoOf (H ⊓ M)
    have hno : D2NoNonExtremalAt P M T := by
      rcases ctx.index_eq_six_or_twelve h27 with h6 | -
      · exact ctx.noNonExtremal_of_index_six h27 h6 hT
      · exact ctx.noNonExtremal_of_l34 hFF h27 hT (hIV.nonExtremalL34At ctx hs h27 hT)
    obtain ⟨hTM, hNTH⟩ := ctx.isSylowTwoOf_of_card27 hFF h27 hT hno.nonExtremalL34At
    have c : D2L34R27 G d P M A H R Rbar K T :=
      ⟨ctx, hs, h27, hT, hno, hTM, hNTH, ctx.conf.not_normalizer_le_of_isSylowTwoOf' hT⟩
    obtain ⟨E, hEP, hE, hE9, hEc⟩ :=
      ctx.exists_center3_of_center3Conclusion (center3_of_solvable27 hX c)
    have h9 := ctx.conf.card_R_eq_nine (ctx.stronglyEmbedded_of_center hEP hE hE9 hEc)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC
