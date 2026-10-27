module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Out
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycRest

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoData.false_of_threeASix_out (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (hThree : KFactBlockThreeASix) (h28 : KFactL28AutThree)
    {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hKax : D1CaseTwoKAxis 3 P M R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hzL : ∀ hzM : (z : G) ∈ M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∉ barM M L) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hzM, hzP, hz3, hCz, hrk, hP4, hcyc, hin⟩ := D1CaseTwoData.nf_inputs hβ hS hKL hInv
    hSch hSyl h84 h85 h86 h93 hD2 hK hd hz hnSP hout hB0 hNH
  obtain ⟨w, hwR, hwC, hwK, hwo, -, -, -, hΩP, -, -⟩ := hKax
  have hstr := D1CaseTwoData.rstruct hβ hS hKL hInv hSch hSyl h28 hd hz hnSP hout hB0 hwR hwC
    hwK hwo
  obtain ⟨-, -, -, -, -, hRz, -⟩ := hz
  have hRP : R ≤ (P : Subgroup G) := fun x hx => hd.cfg.ext.le_P hx
  have hCPR : ∀ g ∈ (P : Subgroup G), g * (z : G) = (z : G) * g → g ∈ R := by
    intro g hgP hgz
    obtain ⟨Q, hQ⟩ := hB0
    have hgC : g ∈ Subgroup.centralizer ({(z : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hgz
    set V := ((P : Subgroup G) ⊓ Subgroup.centralizer ({(z : G)} : Set G)).comap
      (Subgroup.centralizer ({(z : G)} : Set G)).subtype with hV
    have hVp : IsPGroup 3 V := (P.isPGroup'.to_le inf_le_left).comap_subtype
    have hQV : (Q : Subgroup _) ≤ V := by
      intro q hq
      have hqR : (q : G) ∈ R := hQ ▸ ⟨q, hq, rfl⟩
      exact ⟨hRP hqR, q.2⟩
    have hmax := Q.is_maximal' hVp hQV
    have hgV : (⟨g, hgC⟩ : Subgroup.centralizer ({(z : G)} : Set G)) ∈ V := ⟨hgP, hgC⟩
    rw [hmax] at hgV
    exact hQ ▸ ⟨_, hgV, rfl⟩
  exact D1PhaseThree.false_of_threeASix_out h hThree hcyc hzM hzP hz3 hCz hin hrk hP4 hL hZ hA6
    (hzL hzM) hRP hRz hCPR hwR hwo hΩP hstr

@[expose] def D1CaseTwoNormalFormRest6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
          ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
            ζ ≠ 1) →
      (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        Nat.card (Subgroup.center ↥(barM M L)) = 3 →
        ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6))) →
      False

theorem d1CaseTwoNormalFormRest3_of_rest6 (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (hThree : KFactBlockThreeASix) (h28 : KFactL28AutThree)
    (h6 : D1CaseTwoNormalFormRest6) : D1CaseTwoNormalFormRest3 := by
  intro G _ _ p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW
  refine h6 G p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hp3 hW ?_
  intro L hL hZ hA6
  subst hp3
  by_cases hzL : ∃ hzM : (z : G) ∈ M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈
      barM M L
  · exact D1CaseTwoData.false_of_threeASix_mem hβ hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hK
      hThree hd hz hnSP hout hB0 hNH hL hZ hA6 hzL
  · exact D1CaseTwoData.false_of_threeASix_out hβ hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hK
      hThree h28 hd hz hnSP hout hB0 hKax hNH hL hZ hA6 (fun hzM hmem => hzL ⟨hzM, hmem⟩)

end CFSG.AGLEmbedding
