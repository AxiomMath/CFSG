module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Escape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WGood

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]
variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.false_of_thompsonJ_le_of_coprime_of_nine
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (h3 : 3 ≤ Open.pRank 3 M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T)) : False := by
  have := ctx.amb
  exact ctx.conf.false_of_thompsonJ_le_of_coprime_of_card h3 hT hNT hJ hC3
    fun _ hJ1 hJ2 hNJ hE hEel hEc hEp hEcyc =>
      D2L34BetaConf3.card_le_nine_of_good ctx.conf hR9 ctx.normRankTwo
        (⟨_, hJ1, hJ2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (thompsonJ T : Set G))) hNJ
        (hE.trans inf_le_right) (hE.trans inf_le_left) hEp hEcyc
        (ctx.hasGoodE9_of_E27_le le_rfl (hE.trans inf_le_left) hEel (by rw [hEc]; norm_num))

end CFSG.LocalAnalysis.RankThreeTheoremC
