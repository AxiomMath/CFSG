module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBlockFacts
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarTwoA
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFAxis
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFThree
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeInner
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarRes
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem D1CaseTwoDataAt.false_of_three_of_forall (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hInv : KFactCaseTwoInvIn G) (hSch : KFactCatalogSchreier)
    (hSyl : KFactCaseTwoSylow) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK : CitedBlockToralThree) (hKA : CitedBlockToralThreeAut) {P : Sylow 3 G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)} (hd : D1CaseTwoDataAt 3 P M H R Rbar)
    {z : H} (hz : D1CaseTwoCand 3 M H R z) (hnSP : ¬ D1CzSP 3 (z : G))
    (hout : D1CzOutside 3 (z : G)) (hB0 : D1CzB0 3 R (z : G))
    (hNH : Subgroup.normalizer (pCoreOf 2 (GLBPrimeCore 3
      (Subgroup.centralizer ({(z : G)} : Set G))) : Set G) ≤ H)
    (hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ →
      ¬ L ≤ d1X0 3 M H)
    (hZ3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ ζ ∈ barM M L, ζ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
        ζ ^ 3 = 1 → ζ = 1) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hd.toPhaseThree hAut hS hKL
  have hR3 : IsPGroup 3 R := hd.cfg.ext.isPGroup
  have hperf : ∀ U : Subgroup G, U ≤ H ⊓ M → ⁅U, U⁆ = U → Nat.Coprime 3 (Nat.card U) :=
    fun U hU hUp => D1CaseTwoDataAt.coprime_card_of_perfect_of_forall hAut hS hKL hSch hd hall hU
        hUp
  obtain ⟨L₀, hL₀, hL₀X, hzR, hzo, hRz, hzL₀⟩ := id hz
  have hCz := centralizer_le_of_normalizer_vz_le hNH
  have hsyl := exists_sylow_inf_of_sylow hB0 hd.cfg.ext.le_M
  obtain ⟨w, hwR, hwo, hwz, hwc, hwP, -, hΩR, s, hsN, hsz, hsw, hsw1⟩ :=
    D1CaseTwoDataAt.exists_axis_inv hAut hS hKL hInv hSch hSyl hd hz hnSP hout hB0
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
  have hR27 : 3 ^ 3 ≤ Nat.card R := by
    obtain ⟨E, hER, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) R
    have h1 := Subgroup.card_le_of_le hER
    rw [hE] at h1
    exact (Nat.pow_le_pow_right (by norm_num) hd.cfg.ext.three_le_pRank).trans h1
  have hfus := hd.exists_fus_p hzR hzo hRz hB0 (hd.neSylow _ hz hnSP) hwo hwz hwP hΩR
  exact D1PhaseThree.false_of_kline_three h h84 h85 h86 h93 hD2 hK hKA rfl hR3 hperf hZ3 hzR
    hzo hCz hsyl (fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hRz hy)) hwR hwo
    (fun y hy => (hwc y hy).symm) hwz
    (fun g hg hgc hg3 => hΩR g hg (fun y hy => (hgc y hy).symm) hg3) hrk hR27 hfus
    ⟨s, hd.cfg.ext.normalizer_le hsN, hsz, hsinv⟩

end CFSG.AGLEmbedding
