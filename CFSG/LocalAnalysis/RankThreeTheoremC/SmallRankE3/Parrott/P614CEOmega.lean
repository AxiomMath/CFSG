module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CEPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Stage
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_center_of_pRank_le_two {N Q B : Subgroup G} (hN2 : CFSG.Open.pRank 3 N ≤ 2)
    (hQN : Q ≤ N) (hQp : IsPGroup 3 Q) (hBQ : B ≤ Q) (hBe : IsElemAbelian 3 B)
    (hBc : Nat.card B = 3 ^ 2) {q : G} (hqQ : q ∈ Q) (hq3 : q ^ 3 = 1) (hqB : q ∉ B) :
    IsCyclic (Subgroup.center ↥Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnc
  obtain ⟨E₀, hE₀e, hE₀c⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
    (Nat.prime_three.odd_of_ne_two (by norm_num)) (hQp.to_subgroup _) hnc
  set E : Subgroup G := (E₀.map (Subgroup.center ↥Q).subtype).map Q.subtype with hE
  have hEQ : E ≤ Q := Subgroup.map_subtype_le _
  have hEe : IsElemAbelian 3 E := by
    have : CFSG.IsElementaryAbelian 3 ↥E₀ := hE₀e
    have : CFSG.IsElementaryAbelian 3 ↥(E₀.map (Subgroup.center ↥Q).subtype) :=
      CFSG.IsElementaryAbelian.map_subtype
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1
      CFSG.IsElementaryAbelian.map_subtype
  have hEc : Nat.card E = 3 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective Q.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.center ↥Q).subtype_injective, hE₀c]
  have hEcent : ∀ e ∈ E, ∀ w ∈ Q, w * e = e * w := by
    rintro _ ⟨_, ⟨e₀, -, rfl⟩, rfl⟩ w hw
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp e₀.2 ⟨w, hw⟩)
  have hmemE : ∀ w ∈ Q, w ^ 3 = 1 → w ∈ E := fun w hwQ hw3 =>
    mem_of_mem_centralizer_of_pRank_le_two hN2 (hEQ.trans hQN) hEe hEc (hQN hwQ) hw3
      (mem_centralizer_iff.mpr fun e he => (hEcent e he w hwQ).symm)
  have hBE : B ≤ E := fun b hb => hmemE b (hBQ hb) (hBe.2 b hb)
  have hBeq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hEc, hBc])
  exact hqB (by rw [hBeq]; exact hmemE q hqQ hq3)

theorem omegaLe_of_kfact64iii (h64 : KFact64iii) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    (hsit : Sit P M x z) {N T : Subgroup G} (hloc : LocalPair M x z N T)
    (hcore : rankThreePrimeCore 3 N = pCoreOf 2 N) : OmegaLe x z N := by
  intro Q₀ hQ₀N hQ₀p hBQ₀ q hqQ₀ hq3
  by_contra hqB
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hsit.setting
  haveI : IsSimpleGroup G := hS.simple
  have hsit' := hsit.situation
  have hpl := SmallRankPlane.of_situation hS hsit' hsit.point hsit.central
  set B : Subgroup G := zpowers x ⊔ zpowers z with hB
  have hBP : B ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  obtain ⟨Q, hQ₀Q, hQN, hQp, hQidx⟩ := exists_sylow_le_of_isPGroup Nat.prime_three hQ₀N hQ₀p
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q N :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQN, hQp, hQidx⟩
  have hBQ : B ≤ Q := hBQ₀.trans hQ₀Q
  have hqQ : q ∈ Q := hQ₀Q hqQ₀
  have hQM : Q ≤ M := fail614_le_of_plane_le hS hsit.u0 hsit' hBP
    (centralizer_plane_le hS hsit' hsit.point hsit.central) hQp hBQ
  have hN2 : CFSG.Open.pRank 3 N = 2 := by
    refine le_antisymm ?_
      (le_pRank_of_isElemAbelian Nat.prime_three hloc.le hpl.isElemAbelian hpl.card_eq)
    by_contra hbig
    have hQr := pRank_eq_of_sylow Nat.prime_three hQN hQp hQidx
    have h3 : 3 ≤ CFSG.Open.pRank 3 (N ⊓ M) :=
      (show 3 ≤ CFSG.Open.pRank 3 Q by omega).trans
        (pRank_mono 3 Nat.prime_three.one_lt (le_inf hQN hQM))
    exact hloc.not_le (le_of_three_le_pRank_inf hsit.d1 hsit'.mem_sigmaA hsit'.isCoreMaxLocal
      hloc.twoLocal h3)
  obtain ⟨U, hUQ, hUe, hUc, hUr⟩ := sit_exists_plane_centralizer_three hsit hQp hQM hBQ
    hpl.isElemAbelian hpl.card_eq hqQ hq3 hqB
  have hnc : ∀ g ∈ N, B.map (MulAut.conj g).toMonoidHom ≠ U := by
    intro g _ hgU
    have hxU : g * x * g⁻¹ ∈ U := by
      rw [← hgU]
      exact ⟨x, mem_sup_left (mem_zpowers x), rfl⟩
    have hx1 : g * x * g⁻¹ ≠ 1 := fun h => hsit.point.ne_one (conj_eq_one_iff.mp h)
    have h3 := hUr _ hxU hx1
    have h2 : CFSG.Open.pRank 3 (M ⊓ centralizer ({g * x * g⁻¹} : Set G)) ≤ 2 := by
      refine (pRank_mono 3 Nat.prime_three.one_lt inf_le_right).trans ?_
      rw [centralizer_conj_singleton, pRank_map_automorphism 3 Nat.prime_three.one_lt]
      exact sit_pRank_centralizer_point_le_two hsit
    omega
  have hwc : ∀ w ∈ Q, orderOf w = 3 → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ N, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w := by
    intro w hwQ hwo hwcent g _ hgw
    have hw3 : w ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one w
    have hw1 : w ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hwo
      omega
    have hwB : w ∈ B := hpl.mem_of_mem_centralizer w
      (mem_centralizer_iff.mpr fun b hb => hwcent b (hBQ hb)) hw3
    have hwU : w ∈ U := mem_of_mem_centralizer_of_pRank_le_two hN2.le (hUQ.trans hQN) hUe hUc
      (hQN hwQ) hw3 (mem_centralizer_iff.mpr fun u hu => hwcent u (hUQ hu))
    have hwZ : w ∈ zpowers z := by
      by_contra hwZ
      have h2 := sit_pRank_centralizer_le_two_of_mem_plane hsit hwB hwZ
      have h3 := (hUr w hwU hw1).trans (pRank_mono 3 Nat.prime_three.one_lt inf_le_right)
      omega
    have hzw : zpowers w = zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwZ) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hwo,
        orderOf_eq_prime hsit.central.pow_eq_one hsit.central.ne_one]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hzw ▸ mem_zpowers z : z ∈ zpowers w)
    have hgz : g * z * g⁻¹ ∈ B := by
      rw [← hk, ← conj_zpow]
      exact zpow_mem hgw k
    have hgzZ := sit_mem_zpowers_of_conj_mem_plane hsit hgz
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hwZ
    rw [hzw, ← hj, ← conj_zpow]
    exact zpow_mem hgzZ j
  have hU1 : ∀ R : Subgroup G, R ≤ U → 1 ≤ CFSG.Open.pRank 3 R →
      normalizer (R : Set G) ⊓ N ≤ N ⊓ M := by
    intro R hRU hR1 g hg
    refine ⟨hg.2, ?_⟩
    obtain ⟨E, hER, -, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three hR1
    by_cases hRU' : R = U
    · subst hRU'
      exact normalizer_le_of_le_of_two_le_pRank hS hsit.u0 hsit'.mem_sigmaA
        hsit'.isCoreMaxLocal (elementary_isPGroup 3 R hUe) (hUQ.trans hQM)
        (le_pRank_of_isElemAbelian Nat.prime_three le_rfl hUe hUc) hg.1
    ·
      have hRc : Nat.card R = 3 := by
        obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
          (hUc ▸ Subgroup.card_dvd_of_le hRU)
        have h3 : 3 ≤ Nat.card R := by
          have := Subgroup.card_le_of_le hER
          rw [hEc, pow_one] at this
          exact this
        interval_cases k
        · rw [pow_zero] at hk
          omega
        · rw [pow_one] at hk
          exact hk
        · exact absurd (Subgroup.eq_of_le_of_card_ge hRU (by rw [hk, hUc])) hRU'
      have hRne : R ≠ ⊥ := fun h => by
        rw [h, Subgroup.card_bot] at hRc
        omega
      obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
      have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
      have hu3 : (u : G) ^ 3 = 1 := hUe.2 _ (hRU u.2)
      have hRz : zpowers (u : G) = R := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr u.2)
        (by rw [hRc, Nat.card_zpowers, orderOf_eq_prime hu3 hu1'])
      rw [← hRz] at hg
      exact sit_normalizer_zpowers_le hsit (hQM (hUQ (hRU u.2))) hu1' hu3
        (hUr _ (hRU u.2) hu1') hg.1
  have hQ2 : ∀ R : Subgroup G, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R →
      normalizer (R : Set G) ⊓ N ≤ N ⊓ M := fun R hRQ hR2 g hg =>
    ⟨hg.2, normalizer_le_of_le_of_two_le_pRank hS hsit.u0 hsit'.mem_sigmaA
      hsit'.isCoreMaxLocal (hQp.to_le hRQ) (hRQ.trans hQM) hR2 hg.1⟩
  have hYN : N ⊓ M ≠ N := fun h => hloc.not_le (h ▸ inf_le_right)
  have hTM : T ≤ M := by
    by_cases hT1 : T = ⊥
    · rw [hT1]
      exact bot_le
    · have hchar : (T.subgroupOf T).Characteristic := by
        rw [Subgroup.subgroupOf_self]
        infer_instance
      exact Subgroup.le_normalizer.trans (hloc.char_le T le_rfl hT1 hchar)
  have hYT : N ⊓ M ⊔ T ≠ N := by
    rw [sup_eq_left.mpr (le_inf hloc.maxInv.1.1 hTM)]
    exact hYN
  have hKN : CFSG.Open.IsKGroup ↥N :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper N
        (twoLocal_ne_top hS.nonab N hloc.twoLocal))
  obtain ⟨Z₀, hZ₀T, hZ₀1, hZ₀c, hNle⟩ := h64 G N Q B U (N ⊓ M) T hKN hN2 hQsyl
    (isCyclic_center_of_pRank_le_two hN2.le hQN hQp hBQ hpl.isElemAbelian hpl.card_eq hqQ hq3
      hqB)
    hBQ hpl.isElemAbelian (by rw [hpl.card_eq]; norm_num) hUQ hUe (by rw [hUc]; norm_num) hnc
    hwc inf_le_left hYN hU1 hQ2 (hS.charTwo N hloc.twoLocal) hcore hloc.maxInv hYT
  exact hloc.not_le (hNle.trans
    (sup_le inf_le_right (inf_le_right.trans (hloc.char_le Z₀ hZ₀T hZ₀1 hZ₀c))))

theorem omegaFalse_of_kfact64iii (h64 : KFact64iii) (G : Type) [Group G] [Finite G] :
    OmegaFalse G :=
  fun _ _ _ _ hsit _ _ hloc hcore => omegaLe_of_kfact64iii h64 hsit hloc hcore

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614CE
