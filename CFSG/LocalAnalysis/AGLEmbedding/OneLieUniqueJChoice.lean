module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

section Choice

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem exists_uniqueOverJ (hcc : D1ConstrainedCaseAt G) (h1s : D1CaseOneSmallAt G)
    (h2 : D1CaseTwoAt G) (h3 : D1CaseThreeAt G) (hK : KFactOneLie) (hT : KFactOneLieTorus)
    (hd : D1OneLieData p P M H R Rbar K) :
    ∃ (P₀ : Sylow p G) (H₀ R₀ : Subgroup G)
      (Rbar₀ : Sylow p (H₀ ⧸ primeComplementCore (G := H₀) p))
      (K₀ : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) p)),
      D1OneLieData p P₀ M H₀ R₀ Rbar₀ K₀ ∧
        D1UniqueOverJ p H₀ R₀ (nclIn H₀ (d1LiftX p H₀ R₀ K₀)) := by
  obtain ⟨X, ⟨P₁, H₁, R₁, Rb₁, K₁, hd₁, hX₁⟩, hmaxX⟩ := Set.exists_max_image
    {X' : Subgroup G | ∃ (P' : Sylow p G) (H' R' : Subgroup G)
      (Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)),
      D1OneLieData p P' M H' R' Rb' K' ∧ d1LiftX p H' R' K' = X'}
    (fun X' => Nat.card X') (Set.toFinite _) ⟨_, P, H, R, Rbar, K, hd, rfl⟩
  obtain ⟨H₀, ⟨P₀, R₀, Rb₀, K₀, hd₀, hX₀⟩, hmaxJ⟩ := Set.exists_max_image
    {H' : Subgroup G | ∃ (P' : Sylow p G) (R' : Subgroup G)
      (Rb' : Sylow p (H' ⧸ primeComplementCore (G := H') p))
      (K' : Subgroup (H' ⧸ primeComplementCore (G := H') p)),
      D1OneLieData p P' M H' R' Rb' K' ∧ d1LiftX p H' R' K' = X}
    (fun H' => Nat.card (nclIn H' X)) (Set.toFinite _) ⟨H₁, P₁, R₁, Rb₁, K₁, hd₁, hX₁⟩
  subst hX₀
  refine ⟨P₀, H₀, R₀, Rb₀, K₀, hd₀, fun H' hH' hJH' Y hYH' hYp hRY hrk => ?_⟩
  set X := d1LiftX p H₀ R₀ K₀ with hXdef
  obtain ⟨P', R', Rb', K', hd', hle⟩ :=
    hd₀.competitorJ hcc h1s h2 h3 hK hT hH' hJH' hYH' hYp hRY hrk
  have heqX : X = d1LiftX p H' R' K' :=
    Subgroup.eq_of_le_of_card_ge hle (hmaxX _ ⟨P', H', R', Rb', K', hd', rfl⟩)
  have hJJ' : nclIn H₀ X ≤ nclIn H' X :=
    calc nclIn H₀ X = nclIn (nclIn H₀ X) X := hd₀.nclIn_nclIn.symm
      _ ≤ nclIn H' X := nclIn_le_nclIn_of_le (le_nclIn (d1LiftX_le_H p H₀ R₀ K₀)) hJH'
  have heq : nclIn H₀ X = nclIn H' X :=
    Subgroup.eq_of_le_of_card_ge hJJ' (hmaxJ H' ⟨P', R', Rb', K', hd', heqX.symm⟩)
  have h3₀ := hd₀.toPhaseThree hK
  have hJn' : ((nclIn H₀ X).subgroupOf H').Normal := heq ▸ nclIn_normal H' X
  have hAJ : pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) ≤ nclIn H₀ X :=
    (pCoreOf_le 2 _).trans (glbPrimeCore_le p _)
  have hNA : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p (nclIn H₀ X)) : Set G) = H₀ :=
    maxTwoLocal_normalizer_eq_of_normal h3₀.maxTwoLocal_H
      (h3₀.pCoreOf_two_primeCore_ne_bot (d1LiftX_le p H₀ R₀ K₀) hd₀.d1LiftX_ne_bot)
      (pCoreOf_isPGroup 2 _) (hAJ.trans (nclIn_le_self H₀ X))
      (normal_pCoreOf_two_glbPrimeCore p (nclIn_le_self H₀ X) (nclIn_normal H₀ X))
  have hH'H : H' ≤ H₀ := hNA ▸ (Subgroup.normal_subgroupOf_iff_le_normalizer (hAJ.trans hJH')).mp
    (normal_pCoreOf_two_glbPrimeCore p hJH' hJn')
  exact (hH'.2 H₀ h3₀.maxTwoLocal_H.1 hH'H).symm

end Choice

end CFSG.AGLEmbedding
