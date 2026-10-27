module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexMem
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycCover
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarTwoA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem cyc_of_perf
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y)) :
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q := by
  intro V hVB hVp Q hQV hQ3
  obtain ⟨V', hV'le, hV'p, hV'V⟩ := exists_perfect_le_of_le_barM inf_le_right hVB hVp
  have hcop := hperf V' hV'le hV'p
  have hdvd : Nat.card V ∣ Nat.card V' := by
    rw [← hV'V]
    have h1 : Nat.card (barM M V') ∣ Nat.card (V'.subgroupOf M) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (V'.subgroupOf M) = Nat.card V' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hV'le.trans inf_le_right)).toEquiv
    exact h2 ▸ h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ3
  have hQd : 3 ^ k ∣ Nat.card V' := hk ▸ (Subgroup.card_dvd_of_le hQV).trans hdvd
  have hk1 : 3 ^ k = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hcop) hQd
  have hQ1 : Q = ⊥ := Subgroup.eq_bot_of_card_eq Q (hk.trans hk1)
  rw [hQ1]
  infer_instance

theorem card_le_of_not_sp {z : G} (hnSP : ¬ D1CzSP 3 z) :
    ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3 := by
  intro E hEC hE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨m, hm⟩ := hE3.exists_card_eq
  have hle := CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) hEC hE hm
  have h3 : m ≤ 3 := by
    have : ¬ 4 ≤ Open.pRank 3 (Subgroup.centralizer ({z} : Set G)) := hnSP
    omega
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num) h3

theorem D1CaseTwoDataAt.nf_inputs (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoDataAt 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H) :
    D1PhaseThree 3 P M H R ∧ ∃ hzM : (z : G) ∈ M, (z : G) ∈ (P : Subgroup G) ∧
      (z : G) ^ 3 = 1 ∧ Subgroup.centralizer ({(z : G)} : Set G) ≤ H ∧
      (∀ E : Subgroup G, E ≤ Subgroup.centralizer ({(z : G)} : Set G) →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) ∧
      (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
        ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q) ∧
      (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈
          barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h := hd.toPhaseThree hAut hS hKL
  have hcand := hz
  obtain ⟨L₁, hL₁, hL₁X, hzR, hzo, hRz, hzL₁⟩ := hz
  have hCz := centralizer_le_of_normalizer_vz_le hNH
  have hzM : (z : G) ∈ M := hd.cfg.ext.le_M hzR
  have hz3 : (z : G) ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hzpg : IsPGroup 3 (Subgroup.zpowers (z : G)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  set zb := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ with hzb
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨(z : G), hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  have hzN : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      zb ∈ Subgroup.normalizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun L' hL' =>
    mem_normalizer_barM hzM (h.mem_normalizer_block_of_cube hp hp2 h84 h86 hD2 hzM hzpg hz3
      hCz hL')
  refine ⟨h, hzM, hd.cfg.ext.le_P hzR, hz3, hCz, card_le_of_not_sp hnSP, ?_⟩
  by_cases hX : ∃ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₂ ⊤ ∧
      L₂ ≤ d1X0 3 M H
  · obtain ⟨L₂, hL₂, hL₂X⟩ := hX
    obtain ⟨w, hwR, hwo, hwz, hwc, hwP, -, hΩR, -⟩ :=
      D1CaseTwoDataAt.exists_axis_inv hAut hS hKL hInv hSch hSyl hd hcand hnSP hout hB0
    have hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ 3 = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) :=
      fun g hg hgc hg3 => hΩR g hg (fun y hy => (hgc y hy).symm) hg3
    have hLL₂ : L₁ ≠ L₂ := fun he => hL₁X (he ▸ hL₂X)
    have hzL₂ := D1CaseTwoDataAt.mem_component_twoA hd hL₁ hL₂ hLL₂ hzR hzo hzL₁ hwo
      (fun g hg => (hwc g hg).symm) hΩ
    obtain ⟨V, hVp, -, hzV, hVN⟩ :=
      D1CaseTwoDataAt.exists_perfect_blocks hd h hL₂ hL₂X z.2 hzM hzo hzL₂ hzN
    exact ⟨D1CaseTwoDataAt.perf_barM_twoA_cyc hAut hS hKL hSch hd h hL₂ hL₂X,
      fun L' hL' => D1PhaseThree.mem_sup_of_perfect_cat h hSch hL' hVp (hVN L' hL') hzV⟩
  · have hall : ∀ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₂ ⊤ →
        ¬ L₂ ≤ d1X0 3 M H := fun L₂ hL₂ hL₂X => hX ⟨L₂, hL₂, hL₂X⟩
    have hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U) :=
      fun U hU hUp =>
        D1CaseTwoDataAt.coprime_card_of_perfect_of_forall hAut hS hKL hSch hd hall hU hUp
    have hKeq := h.toD1Escape.inf_eq_inf_normalizer_twoCore
    have hperf' : ∀ Y : Subgroup G, Y ≤ M ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) →
        ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y) := fun Y hY hYp => hperf Y (hKeq ▸ hY) hYp
    exact ⟨cyc_of_perf hperf, fun L' hL' => (hK G M (pCoreOf 2 H) L' h.isKGroup.1 h.asc81bHyp hL'
      (h.nineThree h93 hL') (h.nineThree_not_one h85 hD2 hL').1
      (h.not_isSylowTwoOf_inf h85 hD2 hL') hperf' zb (hzN L' hL') hzb3
      (h.not_mem_centralizer_block hp hp2 hzM hzpg hCz hL')
      (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hzpg hCz l hl hl')).1⟩

theorem D1CaseTwoData.nf_inputs (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoData 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H) :
    D1PhaseThree 3 P M H R ∧ ∃ hzM : (z : G) ∈ M, (z : G) ∈ (P : Subgroup G) ∧
      (z : G) ^ 3 = 1 ∧ Subgroup.centralizer ({(z : G)} : Set G) ≤ H ∧
      (∀ E : Subgroup G, E ≤ Subgroup.centralizer ({(z : G)} : Set G) →
        IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3) ∧
      4 ≤ Open.pRank 3 (P : Subgroup G) ∧
      (∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
        ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q) ∧
      (∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈
          barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := by
  obtain ⟨h, hzM, h1, h2, h3, h4, h5, h6⟩ := hd.toAt.nf_inputs (kFactCycAut_of_kFactBeta hβ) hS hKL
    (kFactCaseTwoInvIn_of_kFactCaseTwoInv hInv) hSch hSyl h84 h85 h86 h93 hD2 hK hz hnSP hout hB0
    hNH
  exact ⟨h, hzM, h1, h2, h3, h4,
    CFSG.PreuniquenessRankFour.Helpers.betaFour_all_sylows_rank_ge_four hd.cfg.loc.beta P, h5, h6⟩

theorem D1CaseTwoData.false_of_threeASix_mem (hβ : KFactBeta) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInv) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (hThree : KFactBlockThreeASix) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoData 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hzL : ∃ hzM : (z : G) ∈ M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(z : G), hzM⟩ ∈ barM M L) :
    False := by
  obtain ⟨h, hzM, -, hz3, hCz, hrk, hP4, hcyc, hin⟩ := D1CaseTwoData.nf_inputs hβ hS hKL hInv
    hSch hSyl h84 h85 h86 h93 hD2 hK hd hz hnSP hout hB0 hNH
  obtain ⟨hzM', hzL'⟩ := hzL
  exact D1PhaseThree.false_of_threeASix_mem h hThree hcyc hzM hz3 hCz hin hrk hP4 hL hZ hA6 hzL'

end CFSG.AGLEmbedding
