module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterRest7
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoToralCenterCube
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Rest

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

omit [Finite G] in
theorem barM_inf_le_normalizer :
    barM M (H ⊓ M) ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  rintro _ ⟨m, hm, rfl⟩
  have hmHM : (m : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hm
  exact mem_normalizer_barM m.2 (localGroup_le_normalizer_pCoreOf 2 H hmHM.1)

theorem coprime_of_perf
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y)) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      Nat.Coprime 3 (Nat.card V) := by
  intro V hVB hVp
  obtain ⟨V', hV'le, hV'p, hV'V⟩ := exists_perfect_le_of_le_barM inf_le_right hVB hVp
  have hcop := hperf V' hV'le hV'p
  have hdvd : Nat.card V ∣ Nat.card V' := by
    rw [← hV'V]
    have h1 : Nat.card (barM M V') ∣ Nat.card (V'.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (V'.subgroupOf M) = Nat.card V' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hV'le.trans inf_le_right)).toEquiv
    exact h2 ▸ h1
  exact Nat.Coprime.coprime_dvd_right hdvd hcop

theorem D1CaseTwoData.center_vorcf (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) {P : Sylow 3 G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hd : D1CaseTwoData 3 P M H R Rbar) (h : D1PhaseThree 3 P M H R) {z : H}
    (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G)) (hout : D1CzOutside 3 (z : G))
    (hB0 : D1CzB0 3 R (z : G)) (hzM : (z : G) ∈ M)
    (hCz : Subgroup.centralizer ({(z : G)} : Set G) ≤ H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    (∃ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V, V⁆ = V ∧
        V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈ V) ∨
      ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ blockPL M (pCoreOf 2 H) L → ⁅V, V⁆ = V →
        Nat.Coprime 3 (Nat.card V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcand := hz
  obtain ⟨L₁, hL₁, hL₁X, hzR, hzo, hRz, hzL₁⟩ := hz
  have hz3 : (z : G) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hzpg : IsPGroup 3 (Subgroup.zpowers (z : G)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzN : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈
        Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    mem_normalizer_barM hzM (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hzpg hz3
      hCz hL')
  have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
  have hPLB : blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) := by
    refine barM_mono ?_
    rw [hKeq]
    exact le_inf (inf_le_right.trans hL.le) inf_le_left
  by_cases hX : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₂ ⊤ ∧
      L₂ ≤ d1X0 3 M H
  · obtain ⟨L₂, hL₂, hL₂X⟩ := hX
    obtain ⟨w, hwR, hwo, hwz, hwc, hwP, -, hΩR, -⟩ :=
      D1CaseTwoData.exists_axis_inv hβ hS hKL hInv hSch hSyl hd hcand hnSP hout hB0
    have hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ 3 = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) :=
      fun g hg hgc hg3 => hΩR g hg (fun y hy => (hgc y hy).symm) hg3
    have hLL₂ : L₁ ≠ L₂ := fun he => hL₁X (he ▸ hL₂X)
    have hzL₂ := D1CaseTwoData.mem_component_twoA hd hL₁ hL₂ hLL₂ hzR hzo hzL₁ hwo
      (fun g hg => (hwc g hg).symm) hΩ
    obtain ⟨V, hVp, hVB, hzV, hVN⟩ :=
      D1CaseTwoData.exists_perfect_blocks hd h hL₂ hL₂X z.2 hzM hzo hzL₂ hzN
    exact Or.inl ⟨V, hVp, hVN L hL, hVB.trans barM_inf_le_normalizer, hzV⟩
  · have hall : ∀ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₂ ⊤ →
        ¬ L₂ ≤ d1X0 3 M H := fun L₂ hL₂ hL₂X => hX ⟨L₂, hL₂, hL₂X⟩
    have hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U) :=
      fun U hU hUp => D1CaseTwoData.coprime_card_of_perfect_of_forall hβ hS hKL hSch hd hall hU hUp
    exact Or.inr fun V hV hVp => coprime_of_perf hperf V (hV.trans hPLB) hVp

theorem D1CaseTwoData.false_of_center (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (h28 : KFactL28AutThree) (hBF : CitedBlockToralThreeCenter)
    (hBF2 : CitedBlockToralThreeCenterFix)
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
    (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1) : False := by
  by_cases hc : ∃ y ∈ R, y ^ 3 = (z : G)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨h, hzM, -, hz3, hCz, hrk, hP4, hcyc, hin⟩ := D1CaseTwoData.nf_inputs hβ hS hKL hInv
      hSch hSyl h84 h85 h86 h93 hD2 hK hd hz hnSP hout hB0 hNH
    have hVC := D1CaseTwoData.center_vorcf hβ hS hKL hInv hSch hSyl h84 h86 hD2 hd h hz hnSP hout
      hB0 hzM hCz hL
    obtain ⟨w, hwR, hwo, -, hwc, hwPc, hΩP, hΩR, -⟩ :=
      D1CaseTwoData.exists_axis_inv hβ hS hKL hInv hSch hSyl hd hz hnSP hout hB0
    obtain ⟨-, -, -, hzR, -, hRz, -⟩ := hz
    have hRS : R ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      hd.cfg.ext.le_H.trans (localGroup_le_normalizer_pCoreOf 2 H)
    have hSylR : ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({(z : G)} : Set G) →
        IsPGroup 3 T → Nat.card T ≤ Nat.card R := by
      obtain ⟨Q, hQ⟩ := hB0
      intro T hTC hT3
      have := card_le_card_map_sylow Q hT3 hTC
      rwa [hQ] at this
    exact D1PhaseThree.false_of_center_cube h hBF hBF2 h85 h93 hD2 hcyc hzM hz3 hCz hin hrk hP4
      hno6 hL hζA hζC hζ3 hζ1 hVC (fun x hx => hd.cfg.ext.le_P hx) hRz hRS hSylR
      (hd.cfg.ext.le_P hwR) hwo (hwc _ hzR) hwPc hΩP hΩR hc
  · exact D1CaseTwoData.false_of_center_small hβ hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hK
      h28 hBF hd hz hnSP hout hB0 hKax hNH hno6 hL hζA hζC hζ3 hζ1 hc

theorem d1CaseTwoNormalFormRest6_of_facts (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (h28 : KFactL28AutThree) (hBF : CitedBlockToralThreeCenter)
    (hBF2 : CitedBlockToralThreeCenterFix) : D1CaseTwoNormalFormRest6 := by
  intro G _ _ p P M H R Rbar hd z hz hnSP hout hB0 _ _ hKax hNH hp3 hW h6
  subst hp3
  obtain ⟨L, hL, ζ, hζA, hζC, hζ3, hζ1⟩ := hW
  exact D1CaseTwoData.false_of_center hβ hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hK h28 hBF
    hBF2 hd hz hnSP hout hB0 hKax hNH h6 hL hζA hζC hζ3 hζ1

end CFSG.AGLEmbedding
