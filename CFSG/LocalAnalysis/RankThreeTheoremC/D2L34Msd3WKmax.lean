module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WEscape
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsidePrelim CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

variable {G : Type} [Group G] [Finite G] [D2Amb3 G]

theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_cover_of_nine {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M)
    (hOnly : D2OnlyL34At P M) {J : Subgroup G} (hJH : J ≤ H) (hJgen : J ≤ threePrimeResidual J)
    {E : Subgroup G} (hEJ : E ≤ J) (hEM : E ≤ M) (hEcore : GLBCore 3 1 E ≤ M)
    (hEel : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 2)
    (hKJ : K ≤ (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hJN : J ≤ N) : N = H := by
  have hErank : 2 ≤ Open.pRank 3 E := le_pRank_of_isElemAbelian Nat.prime_three hEel hEc
  exact hc.eq_of_maxTwoLocal_of_cover_of_facts hR9 hOnly hJH hJgen hEJ hEel hEc
    (fun E₀ hE₀p hEE₀ => le_of_pGroup_of_normRankTwo hrk hE₀p hEE₀ hEM hErank) hEcore hKJ hN hJN

theorem D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover_of_nine {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M)
    (hOnly : D2OnlyL34At P M) {C : Subgroup G}
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k)
    {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNC : Subgroup.normalizer (C : Set G) ≤ N) :
    N = H :=
  hc.eq_of_maxTwoLocal_of_normalizer_cover_of_cover
    (fun hJH hJgen hEJ hEM hAW hEel hEc hKJ _ hN hJN =>
      hc.eq_of_maxTwoLocal_of_cover_of_nine hR9 hrk hOnly hJH hJgen hEJ hEM
        (D2L34BetaConf3.core_one_le_of_le_sup hc (fun _ hx => hAW hx) (IsPGroup.of_card hEc) hEc)
        hEel hEc hKJ hN hJN) hcov hN hNC

theorem D2L34BetaConf3.normalizer_le_of_cover_of_nine' {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G}
    {M A H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M)
    (hOnly : D2OnlyL34At P M) {C : Subgroup G} (hC1 : C ≠ ⊥) (hCp : IsPGroup 2 C)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (C : Set G) ≤ H := by
  obtain ⟨N, hNC, hN⟩ := exists_maximal_twoLocal
    (⟨C, hC1, hCp, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C : Set G)))
  exact hNC.trans (D2L34BetaConf3.eq_of_maxTwoLocal_of_normalizer_cover_of_nine hc hR9 hrk hOnly
    hcov hN hNC).le

theorem D2L34BetaConf3.normalizer_le_of_char_cover_of_nine' {d : TauCeti.ValidLieTypeIndex}
    {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hrk : D2NormRankTwo G M)
    (hOnly : D2OnlyL34At P M) {V C : Subgroup G} (hV : IsPGroup 2 V) (hCV : C ≤ V)
    (hC1 : C ≠ ⊥) (hchar : (C.subgroupOf V).Characteristic)
    (hcov : ∀ k ∈ K, ∃ a ∈ H ⊓ Subgroup.normalizer (C : Set G), ∃ ha : a ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨a, ha⟩ = k) :
    Subgroup.normalizer (V : Set G) ≤ H := by
  have hVC : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := V) (C.subgroupOf V)
    rwa [Subgroup.map_subgroupOf_eq_of_le hCV] at h1
  exact hVC.trans (D2L34BetaConf3.normalizer_le_of_cover_of_nine' hc hR9 hrk hOnly hC1
    (hV.to_le hCV) hcov)

end CFSG.LocalAnalysis.RankThreeTheoremC
