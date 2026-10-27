module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Sylow
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterSmall
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRest
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoDataAt.false_of_center_small (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (h28 : KFactL28AutThree) (hBF : CitedBlockToralThreeCenter)
    {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoDataAt 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hKax : D1CaseTwoKAxis 3 P M R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hcube : ¬ ∃ y ∈ R, y ^ 3 = (z : G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h, hzM, -, hz3, hCz, hrk, hcyc, hin⟩ := D1CaseTwoDataAt.nf_inputs hAut hS hKL hInv
    hSch hSyl h84 h85 h86 h93 hD2 hK hd hz hnSP hout hB0 hNH
  obtain ⟨wK, hwKR, hwKC, hwKK, hwKo, hwKz, hwKc, -, -, -, -⟩ := hKax
  have hstr := D1CaseTwoDataAt.rstruct hAut hS hKL hInv hSch hSyl h28 hd hz hnSP hout hB0 hwKR hwKC
    hwKK hwKo
  obtain ⟨w, hwR, hwo, -, hwc, -, hΩP, hΩR, -⟩ :=
    D1CaseTwoDataAt.exists_axis_inv hAut hS hKL hInv hSch hSyl hd hz hnSP hout hB0
  obtain ⟨-, -, -, hzR, hzo, hRz, -⟩ := hz
  rcases hstr with hc | ⟨hcard, a, haR, -, -, har⟩
  · exact hcube hc
  obtain ⟨E, hER, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) R
  have hE27 : 3 ^ 3 ≤ Nat.card E := by
    rw [hEc]
    exact Nat.pow_le_pow_right (by norm_num) hd.cfg.ext.three_le_pRank
  have hsup9 : Nat.card (Subgroup.zpowers wK ⊔ Subgroup.zpowers (z : G) : Subgroup G) =
      3 ^ 2 := by
    have hle : Subgroup.zpowers (z : G) ≤
        Subgroup.centralizer (Subgroup.zpowers wK : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((hwKc _ hzR).zpow_left n).eq
    have hbot := zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hwKo hwKz
    rw [card_sup_of_le_centralizer hle hbot, Nat.card_zpowers, Nat.card_zpowers, hwKo, hzo]
    norm_num
  obtain ⟨r, hrE, hrn⟩ : ∃ r ∈ E, r ∉ Subgroup.zpowers wK ⊔ Subgroup.zpowers (z : G) := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (fun x hx => hcon x hx)
    rw [hsup9] at this
    omega
  have hr3 : r ^ 3 = 1 := hEe.2 r hrE
  have hRS : R ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hd.cfg.ext.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
  have hSylR : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({(z : G)} : Set G) →
      IsPGroup 3 T → Nat.card T ≤ Nat.card R := by
    obtain ⟨Q, hQ⟩ := hB0
    intro T hTC hT3
    have := card_le_card_map_sylow Q hT3 hTC
    rwa [hQ] at this
  exact D1PhaseThree.false_of_center_small h hBF h85 h93 hD2 hcyc hzM hz3 hCz hin hrk hno6 hL
    hζA hζC hζ3 hζ1 (fun x hx => hd.cfg.ext.le_P hx) hRz hRS hSylR (hd.cfg.ext.le_P hwR) hwo
    (hwc _ hzR) hΩP hΩR hcard.le haR (hER hrE) (har r (hER hrE) hr3 hrn)

theorem D1CaseTwoData.false_of_center_small (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (h28 : KFactL28AutThree) (hBF : CitedBlockToralThreeCenter)
    {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData 3 P M H R Rbar) {z : H} (hz : D1CaseTwoCand 3 M H R z)
    (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hKax : D1CaseTwoKAxis 3 P M R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hno6 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      Nat.card (Subgroup.center ↥(barM M L)) = 3 →
      ¬ Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) {ζ : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hζA : ζ ∈ barM M L)
    (hζC : ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) (hcube : ¬ ∃ y ∈ R, y ^ 3 = (z : G)) : False :=
  D1CaseTwoDataAt.false_of_center_small (hAut := (kFactCycAut_of_kFactBeta hβ)) (hS := hS)
    (hKL := hKL) (hInv := (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv)) (hSch := hSch) (hSyl := hSyl)
    (h84 := h84) (h85 := h85) (h86 := h86) (h93 := h93) (hD2 := hD2) (hK := hK) (h28 := h28)
    (hBF := hBF) (hd := hd.toAt) (hz := hz) (hnSP := hnSP) (hout := hout) (hB0 := hB0)
    (hKax := hKax) (hNH := hNH) (hno6 := hno6) (hL := hL) (hζA := hζA) (hζC := hζC) (hζ3 := hζ3)
    (hζ1 := hζ1) (hcube := hcube)

end CFSG.AGLEmbedding
