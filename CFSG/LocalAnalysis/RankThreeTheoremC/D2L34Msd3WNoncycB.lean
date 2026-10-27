module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3NoncycSquare
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.F5Noncyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim
open scoped Pointwise

section Square

variable {G : Type} [Group G] [Finite G]
variable [D2Amb3 G]

theorem exists_inverting_square3_of_good {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    {C₁ : Subgroup G} (hC₁ : C₁ ≠ ⊥) (hC₁2 : IsPGroup 2 C₁)
    (hT₁ : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C₁ : Set G))
    {D : Subgroup G} (hDM : D ≤ M) (hDN : D ≤ Subgroup.normalizer (C₁ : Set G))
    (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D) (hD9 : Nat.card D = 9)
    (hgood : HasGoodE9 M D) :
    ∃ s ∈ M, (∀ x ∈ D, s * x * s⁻¹ ∈ D) ∧ ∀ x ∈ D, s ^ 2 * x * (s ^ 2)⁻¹ = x⁻¹ :=
  exists_inverting_square3_of_escape ctx hT hNT hC₁ hC₁2 hT₁ hDN hD9
    fun _ hN hNM hDN =>
      D2L34BetaConf3.exists_escape_of_good ctx.conf hR9 ctx.normRankTwo hN hNM hDN hDM hDp hDc
        hgood


end Square

section Factor

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem exists_factorization_of_pairData3_of_good
    [D2Amb3 G] {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G}
    {A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K₀) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M)
    {T : Subgroup G} (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) {D : Subgroup G}
    (hDCM : D ≤ Subgroup.centralizer (V : Set G) ⊓ M) (hDp : IsPGroup 3 D) (hDc : ¬ IsCyclic D)
    (hgoodD : HasGoodE9 M D) :
    ∃ B : Subgroup G, B ≤ M ∧ B ≤ Subgroup.normalizer (C₂ : Set G) ∧
      ∀ m ∈ M, ∃ c ∈ Subgroup.centralizer (V : Set G) ⊓ M, ∃ b ∈ B, m = c * b :=
  exists_factorization_of_pairData3_of_card hT hNT hMN hI hcard hSylJ hJM hdat hDCM hDp hDc
    fun hN hNM hQN hQM hQp hQc hDQ =>
      D2L34BetaConf3.card_le_nine_of_good hc hR9 hrk hN hNM hQN hQM hQp hQc (hgoodD.mono hDQ)


end Factor

end CFSG.LocalAnalysis.RankThreeTheoremC
