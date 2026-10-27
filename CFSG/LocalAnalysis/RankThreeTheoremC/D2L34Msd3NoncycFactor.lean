module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Noncyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem exists_factorization_of_pairData3
    [D2Amb3 G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K₀) (hstr : GLBStronglyEmbedded 3 M)
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) {D : Subgroup G}
    (hDCM : D ≤ Subgroup.centralizer (V : Set G) ⊓ M) (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D) :
    ∃ B : Subgroup G, B ≤ M ∧ B ≤ Subgroup.normalizer (C₂ : Set G) ∧
      ∀ m ∈ M, ∃ c ∈ Subgroup.centralizer (V : Set G) ⊓ M, ∃ b ∈ B, m = c * b :=
  exists_factorization_of_pairData3_of_card hT hNT hMN hI hcard hSylJ hJM hdat hDCM hDp hDc
    fun hN hNM hQN hQM hQp hQc _ =>
      D2L34BetaConf3.card_le_nine_of_not_isCyclic hc hstr hN hNM hQN hQM hQp hQc

end CFSG.LocalAnalysis.RankThreeTheoremC
