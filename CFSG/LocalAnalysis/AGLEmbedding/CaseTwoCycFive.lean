module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalFive
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycTransv
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoCycUnique
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEVAx
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFCenter
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFFive
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFPerfect
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPTransvect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_axis_transv (hAut : KFactCycAut) (hSc : KFactSeitzCyc)
    (hL2 : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (hd : D1CaseTwoDataAt p P M H R Rbar) {z : H}
    (hz : D1CaseTwoCand p M H R z) (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G))
    (hB0 : D1CzB0 p R (z : G)) :
    ∃ w ∈ R, orderOf w = p ∧ w ∉ Subgroup.zpowers (z : G) ∧ (∀ g ∈ R, Commute w g) ∧
      (∀ g ∈ R, (∀ h ∈ R, Commute g h) → g ^ p = 1 →
        g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) ∧
      (∃ s ∈ Subgroup.normalizer (R : Set G), s * (z : G) * s⁻¹ = z ∧
        s * w * s⁻¹ ∈ Subgroup.zpowers w ∧ s * w * s⁻¹ ≠ w) ∧
      ∃ x ∈ M, (∃ k : ℕ, x ^ p ^ k = 1) ∧ x * (z : G) * x⁻¹ = z * w ∧ x * w * x⁻¹ = w := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w₀, hwR, hwo, hwz, hwc, hwP, -, hΩR, s, hsN, hsz, hsw, hsw1⟩ :=
    D1CaseTwoDataAt.exists_axis_inv hAut hSc hL2 hInv hSch hSyl hd hz hnSP hout hB0
  obtain ⟨L, hL, hLX, hzR, hzo, hRz, hzL⟩ := hz
  have hQC := hd.inf_centralizer_le hB0
  have hne := hd.neSylow z ⟨L, hL, hLX, hzR, hzo, hRz, hzL⟩ hnSP
  obtain ⟨x, hxP, hxN, hxz⟩ := exists_mem_normalizer_not_mem_zpowers P.isPGroup'
    hd.cfg.ext.le_P hne hzo hQC
  have hxM : x ∈ M := hd.cfg.ext.sylow_le hxP
  have hzc : ∀ g ∈ R, Commute (z : G) g := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hRz hg)).symm
  have hxzR : x * z * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hxN z).mp hzR
  have hxzc : ∀ h ∈ R, Commute (x * z * x⁻¹) h := by
    intro h hh
    have hh' : x⁻¹ * h * x ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) h).mp hh
      simpa using this
    have e := (hzc _ hh').eq
    show x * z * x⁻¹ * h = h * (x * z * x⁻¹)
    calc x * z * x⁻¹ * h = x * (z * (x⁻¹ * h * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * h * x) * z) * x⁻¹ := by rw [e]
      _ = h * (x * z * x⁻¹) := by group
  have hzp : (z : G) ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hxzp : (x * z * x⁻¹) ^ p = 1 := by rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  have hwzc : Commute w₀ z := hwP z (hd.cfg.ext.le_P hzR)
  have hxw : Commute x w₀ := (hwP x hxP).symm
  obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff hwzc).mp (hΩR _ hxzR hxzc hxzp)
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  obtain ⟨m, hm⟩ := P.isPGroup' ⟨x, hxP⟩
  have hxm : x ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hxz' : x * z * x⁻¹ = (z : G) ^ b * w₀ ^ a := by rw [← huv, (hwzc.zpow_zpow a b).eq]
  have hxw' : x * w₀ * x⁻¹ = w₀ := by rw [hxw.eq, mul_inv_cancel_right]
  have hbot : Subgroup.zpowers (z : G) ⊓ Subgroup.zpowers w₀ = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_zpowers_eq_bot_of_not_mem hwo hwz
  have hzb : (z : G) ^ b = z := zpow_eq_self_of_conj hwzc.symm hxz' hxw' hxm hzo hbot
  rw [hzb] at hxz'
  have hwa1 : w₀ ^ a ≠ 1 := fun h1 => hxz (by
    rw [hxz', h1, mul_one]; exact Subgroup.mem_zpowers _)
  have hxu : x * w₀ ^ a * x⁻¹ = w₀ ^ a := by rw [(hxw.zpow_right a).eq, mul_inv_cancel_right]
  have hwap : orderOf (w₀ ^ a) = p := by
    refine orderOf_eq_prime ?_ hwa1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hwo, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨c, hc⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_zpow_ne_one hp hwo hwa1)
  have hw₀ : w₀ ∈ Subgroup.zpowers (w₀ ^ a) := by
    have := Subgroup.zpow_mem_zpowers (w₀ ^ a) c
    rwa [hc] at this
  have heq : Subgroup.zpowers (w₀ ^ a) = Subgroup.zpowers w₀ :=
    le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers w₀ a))
      (Subgroup.zpowers_le.mpr hw₀)
  refine ⟨w₀ ^ a, R.zpow_mem hwR a, hwap, ?_, fun g hg => (hwc g hg).zpow_left a, ?_,
    ⟨s, hsN, hsz, ?_, ?_⟩, x, hxM, ⟨m, hxm⟩, hxz', hxu⟩
  · intro h1
    apply hwz
    rw [← hc]
    exact Subgroup.zpow_mem _ h1 c
  · intro g hg hgc hgp
    rw [heq]
    exact hΩR g hg hgc hgp
  · rw [heq, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
    exact Subgroup.zpow_mem _ hsw a
  · intro h1
    apply hsw1
    rw [← hc, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1]

theorem D1CaseTwoDataAt.false_of_twoA_cyc (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hInn : KFactBlockAutPrimeInner) (hKP : KFactParabolicPrime)
    (hC3 : CitedBlockTransvectionPrime) (hK5 : KFactBlockAltSevenPrime)
    (hK2 : KFactParabolicThree) (hC3' : CitedBlockThreeTransvection)
    (hK5' : KFactBlockThreeAltSeven) (hOP : KFactBlockOutPrime) (hTC : CitedBlockToralCycAut)
    (hd : D1CaseTwoDataAt p P M H R Rbar) {z : H} (hz : D1CaseTwoCand p M H R z)
    (hnSP : ¬ D1CzSP p (z : G)) (hout : D1CzOutside p (z : G)) (hB0 : D1CzB0 p R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore p
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H) (hp5 : 5 ≤ p)
    (hrk3 : Open.pRank 3 (H ⊓ M) ≤ 3)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) : False := by
  have h := hd.toPhaseThree hAut hS hKL
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hRp : IsPGroup p R := hd.cfg.ext.isPGroup
  have hRM : R ≤ M := hd.cfg.ext.le_M
  have hcand := hz
  obtain ⟨L, hL, hLX, hzR, hzo, hRz, hzL⟩ := hz
  have hCz := centralizer_le_of_normalizer_vz_le hNH
  have hzM : (z : G) ∈ M := hRM hzR
  have hzK : (z : G) ∈ H ⊓ M := ⟨z.2, hzM⟩
  have hzp : (z : G) ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
  have hzpg : IsPGroup p (Subgroup.zpowers (z : G)) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hzp)
  set zb := mbar M (z : G) hzM with hzb
  have hzbp : zb ^ p = 1 := by rw [hzb, ← mbar_pow, ← mbar_one]; congr 1
  obtain ⟨w, hwR, hwo, hwz, hwc, hΩR, ⟨s, hsN, hsz, hsw, hsw1⟩, hx⟩ :=
    D1CaseTwoDataAt.exists_axis_transv hAut hS hKL hInv hSch hSyl hd hcand hnSP hout hB0
  have hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) :=
    fun g hg hgc hgp => hΩR g hg (fun y hy => (hgc y hy).symm) hgp
  have hRz' : ∀ y ∈ R, y * (z : G) = (z : G) * y := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hRz hy)
  have hLL₂ : L ≠ L₂ := fun he => hLX (he ▸ hL₂X)
  have hzL₂ := D1CaseTwoDataAt.mem_component_twoA hd hL hL₂ hLL₂ hzR hzo hzL hwo
    (fun g hg => (hwc g hg).symm) hΩ
  obtain ⟨U, hUHM, hUp, hzU⟩ := exists_perfect_cover_of_mem hp hL₂ hL₂X z.2 hzM hzo hzL₂
  have hcyc := D1CaseTwoDataAt.perf_barM_twoA_cyc hAut hS hKL hSch hd h hL₂ hL₂X
  obtain ⟨Lb, hLb⟩ := h.exists_weakSBlock h84 hD2
  have huniq : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M Lb :=
    fun L' hL' => D1PhaseThree.barM_eq_of_perf_cyc_of_pRank h hrk3 h84 h85 h86 h93 hD2 hInn hKP hC3
      hK5 hK2 hC3' hK5' hp5 hzK hzo hCz hcyc L' Lb hL' hLb
  have hKN : ∀ (g : G) (hgM : g ∈ M), g ∈ H →
      mbar M g hgM ∈ Subgroup.normalizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgM hgH
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (barM M Lb).map (MulAut.conj (mbar M g hgM)).toMonoidHom = barM M Lb
    rw [← barM_map_conj hgM Lb]
    exact huniq _ (hLb.map_conj hgM (localGroup_le_normalizer_pCoreOf 2 H hgH))
  have hUM : U ≤ M := hUHM.trans inf_le_right
  set V := barM M U with hV
  have hVp : ⁅V, V⁆ = V := by
    have h1 : ⁅U.subgroupOf M, U.subgroupOf M⁆ = U.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUM, hUp]
    change ⁅(U.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)),
      (U.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))⁆ =
      (U.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rw [← Subgroup.map_commutator, h1]
  have hVL : V ≤ Subgroup.normalizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact hKN u u.2 (hUHM (Subgroup.mem_subgroupOf.mp hu)).1
  have hVS : V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H ⊓ Lb) :
      Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [barM_inf_eq (h.twoCore_M_le h.twoCore_inf)]
    rintro _ ⟨u, hu, rfl⟩
    have huH := (hUHM (Subgroup.mem_subgroupOf.mp hu)).1
    have huS : (u : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      localGroup_le_normalizer_pCoreOf 2 H huH
    have h1 := mem_normalizer_barM u.2 huS
    have h2 := hKN u u.2 huH
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxS, hxL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp h1 x).mp hxS,
        (Subgroup.mem_normalizer_iff.mp h2 x).mp hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp h1 x).mpr hxS,
        (Subgroup.mem_normalizer_iff.mp h2 x).mpr hxL⟩
  have hzV : zb ∈ V := ⟨⟨(z : G), hzM⟩, Subgroup.mem_subgroupOf.mpr hzU, rfl⟩
  have hzN : zb ∈ Subgroup.normalizer (barM M Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hzM (h.mem_normalizer_block_of_five_of_pRank hrk3 h85 h86 h93 hD2 hK2 hC3'
        hK5' hp5
      hzK hzo hLb)
  have hin := D1PhaseThree.mem_sup_of_perfect h h85 h93 hD2 hOP hSch hp5 hLb hzN hzbp hVp hVL
    hzV
  have hPL : ∀ W : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      W ≤ blockPL M (pCoreOf 2 H) Lb →
      ⁅W, W⁆ = W → ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ W → IsPGroup p Q →
        IsCyclic Q := by
    intro W hW hWp
    refine hcyc W (hW.trans (barM_mono ?_)) hWp
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hLb.le
  obtain ⟨hZ, htr⟩ := hTC G M (pCoreOf 2 H) Lb p h.isKGroup.1 h.asc81bHyp hLb
    (h.nineThree h93 hLb) (h.nineThree_not_one h85 hD2 hLb).1
    (h.not_isSylowTwoOf_inf h85 hD2 hLb) hp hp5 hPL zb hin hzbp
    (h.not_mem_centralizer_block hp hp2 hzM hzpg hCz hLb) ⟨V, hVp, hVL, hVS, hzV⟩
    (fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hzpg hCz l hl hl')
  have hsyl := exists_sylow_inf_of_sylow hB0 hRM
  exact D1PhaseThree.false_of_kline_transv h hRp hLb huniq hZ hzR hzo htr hCz hsyl hin hRz'
    hwR hwo hwz hΩ hx ⟨s, hd.cfg.ext.normalizer_le hsN, hsz, hsw, hsw1⟩

end CFSG.AGLEmbedding
