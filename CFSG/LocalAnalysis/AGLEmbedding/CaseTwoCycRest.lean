module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarTwoA
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycCover
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycFive
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycThree
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFRest
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeBlockRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoDataAt.false_of_twoA_three (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hTC3 : CitedBlockToralThreeCyc) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoDataAt 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 3 M H)
    (hZ3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ζ ^ 3 = 1 → ζ = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h := hd.toPhaseThree hAut hS hKL
  have hR3 : IsPGroup 3 R := hd.cfg.ext.isPGroup
  have hRM : R ≤ M := hd.cfg.ext.le_M
  have hcand := hz
  obtain ⟨L, hL, hLX, hzR, hzo, hRz, hzL⟩ := hz
  have hCz := centralizer_le_of_normalizer_vz_le hNH
  have hsyl := exists_sylow_inf_of_sylow hB0 hRM
  have hzM : (z : G) ∈ M := hRM hzR
  have hz3 : (z : G) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hzpg : IsPGroup 3 (Subgroup.zpowers (z : G)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  set zb := mbar M (z : G) hzM with hzb
  have hzb3 : zb ^ 3 = 1 := by rw [hzb, ← mbar_pow, ← mbar_one]; congr 1
  obtain ⟨w, hwR, hwo, hwz, hwc, hwP, -, hΩR, s, hsN, hsz, hsw, hsw1⟩ :=
    D1CaseTwoDataAt.exists_axis_inv hAut hS hKL hInv hSch hSyl hd hcand hnSP hout hB0
  have hsinv : s * w * s⁻¹ = w⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsw
    have hk' : w ^ (k % 3) = s * w * s⁻¹ := by rw [zpow_mod_three hwo, hk]
    have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk3 with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hk'
      have : w = 1 := by
        have e : w = s⁻¹ * (s * w * s⁻¹) * s := by group
        rw [e, ← hk']; group
      rw [this, orderOf_one] at hwo
      exact absurd hwo (by norm_num)
    · exact absurd (by rw [← hk', h1, zpow_one]) hsw1
    · rw [← hk', h2]
      have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, hw3]
  have hrk : ∀ E : Subgroup G, E ≤ R → IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := by
    intro E hER hE
    obtain ⟨m, hm⟩ := (hR3.to_le hER).exists_card_eq
    have hle := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) (hER.trans hRz) hE hm
    have h3 : m ≤ 3 := by
      have : ¬ 4 ≤ Open.pRank 3 (Subgroup.centralizer ({(z : G)} : Set G)) := hnSP
      omega
    rw [hm]
    exact Nat.pow_le_pow_right (by norm_num) h3
  have hfus := hd.exists_fus_p hzR hzo hRz hB0 (hd.neSylow _ hcand hnSP) hwo hwz hwP
    hΩR
  have hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) :=
    fun g hg hgc hg3 => hΩR g hg (fun y hy => (hgc y hy).symm) hg3
  have hLL₂ : L ≠ L₂ := fun he => hLX (he ▸ hL₂X)
  have hzL₂ := D1CaseTwoDataAt.mem_component_twoA hd hL hL₂ hLL₂ hzR hzo hzL hwo
    (fun g hg => (hwc g hg).symm) hΩ
  have hzN : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      zb ∈ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    mem_normalizer_barM hzM (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hzpg hz3
      hCz hL')
  obtain ⟨V, hVp, hVB, hzV, hVN⟩ :=
    D1CaseTwoDataAt.exists_perfect_blocks hd h hL₂ hL₂X z.2 hzM hzo hzL₂ hzN
  have hin : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      zb ∈ barM M L' ⊔ Subgroup.centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L' hL' => D1PhaseThree.mem_sup_of_perfect_cat h hSch hL' hVp (hVN L' hL') hzV
  have hVS : V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro v hv
    obtain ⟨⟨g, hgM⟩, hg, rfl⟩ := hVB hv
    exact mem_normalizer_barM hgM
      (localGroup_le_normalizer_pCoreOf 2 H (Subgroup.mem_subgroupOf.mp hg).1)
  have hVSL : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H ⊓ L') : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro L' hL' v hv
    rw [barM_inf_eq (h.twoCore_M_le h.twoCore_inf)]
    have h1 := hVS hv
    have h2 := hVN L' hL' hv
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    constructor
    · rintro ⟨hxS, hxL⟩
      exact ⟨(h1 x).mp hxS, (h2 x).mp hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨(h1 x).mpr hxS, (h2 x).mpr hxL⟩
  have hcyc := D1CaseTwoDataAt.perf_barM_twoA_cyc hAut hS hKL hSch hd h hL₂ hL₂X
  have hE : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → zb ∈ barM M L' →
      ∀ v ∈ barM M L', v ^ 3 = 1 → v * zb = zb * v → v ∈ Subgroup.zpowers zb := by
    intro L' hL' hzL' v hv hv3 hvc
    have hPL : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), W ≤ blockPL M (pCoreOf 2 H) L' →
        ⁅W, W⁆ = W → ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ W → IsPGroup 3 Q →
          IsCyclic Q := by
      intro W hW hWp
      refine hcyc W (hW.trans (barM_mono ?_)) hWp
      rw [h.normalizer_twoCore_H]
      exact inf_le_inf_left H hL'.le
    exact hTC3 G M (pCoreOf 2 H) L' h.isKGroup.1 h.asc81bHyp hL' (h.nineThree h93 hL')
      (h.nineThree_not_one h85 hD2 hL').1 (h.not_isSylowTwoOf_inf h85 hD2 hL') hPL
      (hZ3 L' hL') zb hzL' hzb3 (h.not_mem_centralizer_block hp hp2 hzM hzpg hCz hL')
      ⟨V, hVp, hVN L' hL', hVSL L' hL', hVS, hzV⟩
      (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hzpg hCz l hl hl') v hv hv3 hvc
  exact D1PhaseThree.false_of_kline_three_cyc h h84 hD2 rfl hR3 hZ3 hzR hzo hCz hsyl
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hRz hy)) hwR hwo
    (fun y hy => (hwc y hy).symm) hwz hΩ hrk hfus
    ⟨s, hd.cfg.ext.normalizer_le hsN, hsz, hsinv⟩ hin hE

@[expose] def D1CaseTwoNormalFormRest3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    ∀ z : H, D1CaseTwoCand p M H R z → ¬ D1CzSP p (z : G) → D1CzOutside p (z : G) →
      D1CzB0 p R (z : G) → pCoreOf 2 M ⊓ Subgroup.centralizer ({(z : G)} : Set G) ≠ ⊥ →
      D1CzEven p (z : G) → D1CaseTwoKAxis p P M R (z : G) →
      Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
        (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H →
      p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
          ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
            ζ ≠ 1) → False

theorem D1CaseTwoDataAt.false_of_nfTwoA {G : Type} [Group G] [Finite G] (hAut : KFactCycAut)
    (hS : KFactSeitzCyc) (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G)
    (hSch : KFactCatalogSchreier) (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hOP : KFactBlockOutPrime) (hK : CitedBlockToralThree)
    (hKA : CitedBlockToralThreeAut) (hTC : CitedBlockToralCycAut)
    (hTC3 : CitedBlockToralThreeCyc) {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)} (hd : D1CaseTwoDataAt p P M H R Rbar) {z
        : H}
    (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G))
    (hB0 : D1CzB0 p R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hpX : p = 3 ∨ ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≤
        d1X0 p M H)
    (hrk3 : 3 < p → Open.pRank 3 (H ⊓ M) ≤ 3)
    (h3 : p = 3 → (∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
      ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧
        ζ ≠ 1) → False) : False := by
  by_cases hp3 : p = 3
  · by_cases hW : ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ ∃ ζ ∈ barM M L,
        ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ ζ ^ 3 = 1 ∧ ζ ≠ 1
    · exact h3 hp3 hW
    have hZ3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
          ζ ^ 3 = 1 → ζ = 1 := by
      intro L hL ζ hζ hζC hζ3
      by_contra hne
      exact hW ⟨L, hL, ζ, hζ, hζC, hζ3, hne⟩
    subst hp3
    by_cases hX : ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ ∧
        L ≤ d1X0 3 M H
    · obtain ⟨L₂, hL₂, hL₂X⟩ := hX
      exact D1CaseTwoDataAt.false_of_twoA_three hAut hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hTC3
        hd hz hnSP hout hB0 hNH hL₂ hL₂X hZ3
    exact D1CaseTwoDataAt.false_of_three_of_forall hAut hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hK
      hKA hd hz hnSP hout hB0 hNH (fun L hL hLX => hX ⟨L, hL, hLX⟩) hZ3
  obtain ⟨L₂, hL₂, hL₂X⟩ := hpX.resolve_left hp3
  have hp5 := hd.cfg.red.prime.five_le_of_ne_two_of_ne_three hd.cfg.red.ne_two hp3
  exact D1CaseTwoDataAt.false_of_twoA_cyc hAut hS hKL hInv hSch hSyl h84 h85 h86 h93 hD2 hInn hKP
    hC3 hK5 hK2 hC3' hK5' hOP hTC hd hz hnSP hout hB0 hNH
    hp5 (hrk3 (by omega)) hL₂ hL₂X

theorem d1CaseTwoNormalFormTwoA_of_rest3 (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hOP : KFactBlockOutPrime) (hK : CitedBlockToralThree)
    (hKA : CitedBlockToralThreeAut) (hTC : CitedBlockToralCycAut)
    (hTC3 : CitedBlockToralThreeCyc) (h3 : D1CaseTwoNormalFormRest3) :
    D1CaseTwoNormalFormTwoA :=
  fun G _ _ p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH hpX =>
    hd.toAt.false_of_nfTwoA (kFactCycAut_of_kFactBeta hβ) hS hKL
      (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hSyl h84 h85 h86 h93 hD2 hInn hKP hC3 hK5
      hK2 hC3' hK5' hOP hK hKA hTC hTC3 hz hnSP hout hB0 hNH hpX
      (fun hp => by
        by_contra hc
        exact (hd.toPhaseThree hβ hS hKL).false_of_four_le_pRank' hd.cfg.ind Nat.prime_three
          (by decide) hp (by omega))
      (h3 G p P M H R Rbar hd z hz hnSP hout hB0 hQ hEv hKax hNH)

end CFSG.AGLEmbedding
