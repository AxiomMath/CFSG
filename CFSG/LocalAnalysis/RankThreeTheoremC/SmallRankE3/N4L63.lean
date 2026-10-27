module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N4Sit
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5LargeSteps
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L63Core
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Setting

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

@[expose] def NoTwoComponentsGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → ∀ (p : ℕ), 5 ≤ p → ∀ (P : Sylow p G) (M : Subgroup G),
    SmallRankSituation G p P M → ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
    ¬ ∃ L K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
      IsComponentOf L ⊤ ∧ p ∣ Nat.card L ∧ IsComponentOf K ⊤ ∧ K ≠ L

@[expose] def KFactSingleW : Prop :=
  ∀ (p : ℕ) (X : Type) [Group X] [Finite X] (P : Sylow p X) (x z : X),
    N3.Plane63E3 p X P x z →
    (∀ (N : Subgroup X) [N.Normal], IsPGroup p (X ⧸ N) → N = ⊤) →
    (∃ L : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (X ⧸ primeComplementCore (G := X) p), IsComponentOf K ⊤ → K = L) →
    ∀ W : Subgroup X, Nat.Coprime p (Nat.card W) →
      zpowers x ⊔ zpowers z ≤ normalizer (W : Set X) → W ≤ primeComplementCore (G := X) p

theorem slotP614NormalizerRankLarge_of_kfacts (hβ : NoTwoComponentsGen) (hK : KFactSingleW) :
    SlotP614NormalizerRankLarge := by
  intro G _ _ hS hD1 p hp5 P M hsit x z hx hz hcon T hT
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp2 : p ≠ 2 := sigmaA_odd p hsit.mem_sigmaA
  obtain ⟨hPM, hxM, hzM, hpl⟩ := n4_plane63E3 hS hsit hp5 hx hz
  have hne : M ≠ ⊤ := fun h => hx.not_centralizer_le (h ▸ le_top)
  have hBM : zpowers x ⊔ zpowers z ≤ M :=
    sup_le (zpowers_le.mpr hxM) (zpowers_le.mpr hzM)
  have hT' := isMaxTwoInvariantIn_top hBM hT
  rw [← plane_eq_subgroupOf (⟨x, hxM⟩ : M) ⟨z, hzM⟩] at hT'
  suffices hkey : Open.pRank p ((P.subtype hPM : Sylow p M) : Subgroup M) ≤
      Open.pRank p (normalizer ((T.subgroupOf M : Subgroup M) : Set M)) by
    rw [pRank_normalizer_subgroupOf hprime.one_lt hT.1.1] at hkey
    change Open.pRank p ((P : Subgroup G).subgroupOf M) ≤ _ at hkey
    rwa [pRank_subgroupOf hprime.one_lt hPM] at hkey
  obtain ⟨L₀, hL₀, -, -, hpL₀, -, -⟩ :=
    CFSG.AGLEmbedding.isKProper_not_hasPrimeConstraint_catalog_component hS.kProper M hne p hprime
      hcon
  by_cases huniq : ∃ L : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p), IsComponentOf L ⊤ ∧
      ∀ K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p), IsComponentOf K ⊤ → K = L
  · have h2 := hK p M (P.subtype hPM) ⟨x, hxM⟩ ⟨z, hzM⟩ hpl
      (fun N _ hN => n4_eq_top_of_isPGroup_quotient hS hsit N hN) huniq
    have hcop : Nat.Coprime p (Nat.card (T.subgroupOf M)) := by
      obtain ⟨k, hk⟩ := (hT'.1.2.1 : IsPGroup 2 (T.subgroupOf M)).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes hprime Nat.prime_two).mpr hp2)
    have hBinv : zpowers (⟨x, hxM⟩ : M) ⊔ zpowers (⟨z, hzM⟩ : M) ≤
        normalizer ((T.subgroupOf M : Subgroup M) : Set M) := hT'.1.2.2
    exact normalizerRank_of_le_core hprime hp2 (hpl.plane.isIsolatedPlane.1) hT'
      (h2 _ hcop hBinv)
  · exfalso
    obtain ⟨K, hK', hKL⟩ : ∃ K : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) p),
        IsComponentOf K ⊤ ∧ K ≠ L₀ := by
      by_contra hno
      push Not at hno
      exact huniq ⟨L₀, hL₀, hno⟩
    exact hβ G hS p hp5 P M hsit x z hx hz ⟨L₀, K, hL₀, hpL₀, hK', hKL⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
