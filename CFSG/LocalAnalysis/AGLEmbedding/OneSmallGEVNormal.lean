module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def KFactSmallGammaSolvableSpor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      ¬ IsSmallLinTwo p K → ¬ IsSmallUnitary p K → ¬ IsAltTwoP p K →
      ¬ (p = 3 ∧ IsLinThreeFour K) → ¬ (p = 5 ∧ IsFi22 K) →
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

@[expose] def D1SmallGEVNormalThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K) → ¬ (p = 3 ∧ IsSmallUnitary 3 K) →
    ¬ (p = 3 ∧ IsLinThreeFour K) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    p = 3 → False

@[expose] def D1SmallGEVNormalAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K → ¬ (p = 5 ∧ IsFi22 K) →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    5 ≤ p → IsAltTwoP p K → False

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem D1OneSmallData.false_of_centralizer_le_five {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hUP : KFactUPrimeSmall)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hInn : KFactBlockAutPrimeInner)
    (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K)
    (hL : ¬ (p = 3 ∧ IsLinThreeFour K)) (hF : ¬ (p = 5 ∧ IsFi22 K)) (hp5 : 5 ≤ p)
    {T₁ : Sylow p K} (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    (hout : Group.IsSolvable (Outer K)) (hs : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)))
    {z : G} (hz : D1SmallCZElt p H R K z) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H) :
    False := by
  have h3 := hd.toPhaseThree hUP hL hF
  obtain ⟨T, -, hs', hn, hc, hTnc, hΓ, -⟩ := hd.exists_sylow
  have hUPK : KFactUPrime p K :=
    hUP K hs' hn hc p hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ hd.small hL hF
  exact h3.false_of_centralizer_le_five hd.cfg.ind h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5'
    hInn hp5 (fun U hU hUp => hd.coprime_card_of_perfect hI hT₁ hUPK hout hs hU hUp)
    (h3.le_inf hz.1) hz.2.1 hCz

theorem d1SmallGEVNormal_of_residues (hUP : KFactUPrimeSmall) (hSch : KFactCatalogSchreier)
    (hK8 : KFactSmallBorelSolvable) (hΓ : KFactSmallGammaSolvableSpor)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hInn : KFactBlockAutPrimeInner)
    (h3r : D1SmallGEVNormalThree) (hAr : D1SmallGEVNormalAlt) : D1SmallGEVNormal := by
  intro G _ _ p P M H R Rbar K hd z hz hI hB0 hEv hIso hA6 hU3 hL hFi hAlt hcomm hQz hNV hCz
    hOz hnorm
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  rcases Nat.lt_or_ge p 5 with hp5 | hp5
  · have hp3 : p = 3 := by
      have := hp.two_le
      interval_cases p
      · exact absurd rfl hp2
      · rfl
      · exact absurd hp (by decide)
    exact h3r G p P M H R Rbar K hd z hz hI hB0 hEv hIso hA6 hU3 hL hcomm hQz hNV hCz hOz hnorm
      hp3
  by_cases hA : IsAltTwoP p K
  · exact hAr G p P M H R Rbar K hd z hz hI hB0 hEv hIso hFi hAlt hcomm hQz hNV hCz hOz hnorm hp5
      hA
  have hL' : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => by omega
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT, -⟩ := hd.exists_sylow
  have hout := hSch K hs hn hc
  have hsolv : Group.IsSolvable (GLBCore p 1 (T₁ : Subgroup K)) := by
    by_cases hfam : IsSmallLinTwo p K ∨ IsSmallUnitary p K
    · exact hK8 K p hp hp5 hfam T₁
    · push Not at hfam
      exact hΓ K hs hn hc p hp hp2 T₁ hTnc hΓT hd.small hfam.1 hfam.2 hA hL' hFi
  exact hd.false_of_centralizer_le_five hUP h84 h85 h86 h93 hD2 hKP hC3 hK5 hK2 hC3' hK5' hInn
    hI hL' hFi hp5 hT₁ hout hsolv hz hCz

end CFSG.AGLEmbedding
