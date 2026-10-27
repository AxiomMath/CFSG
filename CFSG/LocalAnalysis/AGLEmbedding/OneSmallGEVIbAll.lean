module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1SmallGEVIbNormalAllRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ D1SmallOuterR p H Rbar K →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) →
    (p = 3 ∨ Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) ≠ p ^ 2 ∨ IsAltTwoP p K ∨
      (p = 5 ∧ IsFi22 K)) → False

theorem d1SmallGEVIbNormalAll_of_rest (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hK8 : KFactSmallBorelSolvable) (hΓs : KFactSmallGammaSolvableSpor)
    (hOut : KFactSmallOutPPrime) (hExp : KFactSmallSylowExp) (hOrb : KFactSmallOrbits)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (hB : D1IbBlockInputs) (hRest : D1SmallGEVIbNormalAllRest) : D1SmallGEVIbNormalAll := by
  intro G _ _ p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm hall
  by_cases hcase : p = 3 ∨ Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) p)) ≠ p ^ 2 ∨ IsAltTwoP p K ∨
    (p = 5 ∧ IsFi22 K)
  · exact hRest G p P M H R Rbar K hd z hz hnIa hB0 hEv hIso hOR hgp hcomm hnot hH hVH hsm hall
      hcase
  push Not at hcase
  obtain ⟨hp3, hT2, hA, hFi⟩ := hcase
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 5 with h | h
    · interval_cases p
      · exact absurd rfl hp2
      · exact absurd rfl hp3
      · exact absurd hp (by decide)
    · exact h
  exact D1OneSmallData.false_of_ibNormal hUP hSch hK8 hΓs hOut hExp hOrb hInn hKP hC3p hK5p hB hd
    hz hnIa hB0 (fun h => hp3 h.1) hVH hp5 hT2 hA (fun h => hFi h.1 h.2)

end CFSG.AGLEmbedding
