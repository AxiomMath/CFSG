module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K278Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CEPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614CEOmega
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure Data278 (M H : Subgroup G) (x z : G) (Q K : Subgroup G) : Prop where
  syl : CFSG.ABGLocalTools.IsSylowOf 3 Q H
  le_M : Q ≤ M
  plane_le : zpowers x ⊔ zpowers z ≤ Q
  card_ge : 27 ≤ Nat.card Q
  rank : CFSG.Open.pRank 3 H = 2
  z_central : ∀ g ∈ Q, g * z = z * g
  gamma : ∀ R : Subgroup G, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R →
    normalizer (R : Set G) ⊓ H ≤ H ⊓ M
  K_le : K ≤ H
  K_normal : H ≤ normalizer (K : Set G)
  K_max : ∀ N : Subgroup G, N ≤ K → (N.subgroupOf K).Normal → K ⊓ rankThreePrimeCore 3 H ≤ N →
    N = K ⊓ rankThreePrimeCore 3 H ∨ N = K
  cover : H ≤ ((H ⊓ M) ⊔ K) ⊔ rankThreePrimeCore 3 H
  iso : Nonempty (Kbar K ≃* PSL(3, GaloisField 2 2))

theorem exists_data278 (k278 : KFact278L34) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    {H S : Subgroup G} (hyp : Hyp P M x z H S) {Q₀ : Subgroup G} (hQ₀H : Q₀ ≤ H)
    (hQ₀p : IsPGroup 3 Q₀) (hBQ₀ : zpowers x ⊔ zpowers z ≤ Q₀) {q : G} (hqQ₀ : q ∈ Q₀)
    (hq3 : q ^ 3 = 1) (hqB : q ∉ zpowers x ⊔ zpowers z) :
    ∃ Q K : Subgroup G, Data278 M H x z Q K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsit : Sit P M x z :=
    ⟨hyp.setting, hyp.u0, hyp.d1, hyp.situation, hyp.point, hyp.central⟩
  have hS := hyp.setting
  haveI : IsSimpleGroup G := hS.simple
  have hsit' := hyp.situation
  have hpl := SmallRankPlane.of_situation hS hsit' hyp.point hyp.central
  set B : Subgroup G := zpowers x ⊔ zpowers z with hB
  have hBH : B ≤ H := hyp.optimal.ext.pair.le
  obtain ⟨Q, hQ₀Q, hQH, hQp, hQidx⟩ := exists_sylow_le_of_isPGroup Nat.prime_three hQ₀H hQ₀p
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 Q H :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hQH, hQp, hQidx⟩
  have hBQ : B ≤ Q := hBQ₀.trans hQ₀Q
  have hqQ : q ∈ Q := hQ₀Q hqQ₀
  have hQM : Q ≤ M := hyp.optimal.sylow_le Q hQp hQH hBQ
  have hQ27 : 27 ≤ Nat.card Q := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    have h9 : 3 ^ 2 ∣ 3 ^ n := by
      rw [← hpl.card_eq, ← hn]
      exact Subgroup.card_dvd_of_le hBQ
    have hn2 : 2 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h9
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have hQB : Q = B := (Subgroup.eq_of_le_of_card_ge hBQ (by
        rw [hn, hpl.card_eq, show n = 2 by omega])).symm
      exact hqB (hQB ▸ hqQ)
    rw [hn]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have hH2 : CFSG.Open.pRank 3 H = 2 := le_antisymm hyp.optimal.pRank_le
    (le_pRank_of_isElemAbelian Nat.prime_three hBH hpl.isElemAbelian hpl.card_eq)
  obtain ⟨U, hUQ, hUe, hUc, hUr⟩ := P614CE.sit_exists_plane_centralizer_three hsit hQp hQM hBQ
    hpl.isElemAbelian hpl.card_eq hqQ hq3 hqB
  have hnc : ∀ g ∈ H, B.map (MulAut.conj g).toMonoidHom ≠ U := by
    intro g _ hgU
    have hxU : g * x * g⁻¹ ∈ U := by
      rw [← hgU]
      exact ⟨x, mem_sup_left (mem_zpowers x), rfl⟩
    have hx1 : g * x * g⁻¹ ≠ 1 := fun h => hyp.point.ne_one (conj_eq_one_iff.mp h)
    have h3 := hUr _ hxU hx1
    have h2 : CFSG.Open.pRank 3 (M ⊓ centralizer ({g * x * g⁻¹} : Set G)) ≤ 2 := by
      refine (pRank_mono 3 Nat.prime_three.one_lt inf_le_right).trans ?_
      rw [P614CE.centralizer_conj_singleton, pRank_map_automorphism 3 Nat.prime_three.one_lt]
      exact P614CE.sit_pRank_centralizer_point_le_two hsit
    omega
  have hcentZ : ∀ w ∈ Q, w ^ 3 = 1 → w ≠ 1 → (∀ q ∈ Q, q * w = w * q) → w ∈ zpowers z := by
    intro w hwQ hw3 hw1 hwcent
    have hwB : w ∈ B := hpl.mem_of_mem_centralizer w
      (mem_centralizer_iff.mpr fun b hb => hwcent b (hBQ hb)) hw3
    have hwU : w ∈ U := P614CE.mem_of_mem_centralizer_of_pRank_le_two hH2.le (hUQ.trans hQH)
      hUe hUc (hQH hwQ) hw3 (mem_centralizer_iff.mpr fun u hu => hwcent u (hUQ hu))
    by_contra hwZ
    have h2 := P614CE.sit_pRank_centralizer_le_two_of_mem_plane hsit hwB hwZ
    have h3 := (hUr w hwU hw1).trans (pRank_mono 3 Nat.prime_three.one_lt inf_le_right)
    omega
  have hwc : ∀ w ∈ Q, orderOf w = 3 → (∀ q ∈ Q, q * w = w * q) →
      ∀ g ∈ H, g * w * g⁻¹ ∈ B → g * w * g⁻¹ ∈ zpowers w := by
    intro w hwQ hwo hwcent g _ hgw
    have hw3 : w ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one w
    have hw1 : w ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hwo
      omega
    have hwZ := hcentZ w hwQ hw3 hw1 hwcent
    have hzw : zpowers w = zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwZ) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hwo,
        orderOf_eq_prime hyp.central.pow_eq_one hyp.central.ne_one]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hzw ▸ mem_zpowers z : z ∈ zpowers w)
    have hgz : g * z * g⁻¹ ∈ B := by
      rw [← hk, ← conj_zpow]
      exact zpow_mem hgw k
    have hgzZ := P614CE.sit_mem_zpowers_of_conj_mem_plane hsit hgz
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hwZ
    rw [hzw, ← hj, ← conj_zpow]
    exact zpow_mem hgzZ j
  have hzc : ∀ g ∈ Q, g * z = z * g := by
    haveI : Nontrivial ↥Q := ⟨⟨⟨z, hBQ (mem_sup_right (mem_zpowers z))⟩, 1, fun h =>
      hyp.central.ne_one (congrArg Subtype.val h)⟩⟩
    have hQp' : IsPGroup 3 ↥Q := hQp
    haveI : Nontrivial (center ↥Q) := hQp'.center_nontrivial
    obtain ⟨n, hn0, hn⟩ := (hQp'.to_subgroup (center ↥Q)).nontrivial_iff_card.mp inferInstance
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(center ↥Q)) 3
      (by rw [hn]; exact dvd_pow_self 3 hn0.ne')
    have hwcent : ∀ g ∈ Q, g * ((w : ↥Q) : G) = ((w : ↥Q) : G) * g := fun g hg =>
      congrArg Subtype.val (mem_center_iff.mp w.2 ⟨g, hg⟩)
    have hwo : orderOf ((w : ↥Q) : G) = 3 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
    have hw3 : ((w : ↥Q) : G) ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one _
    have hw1 : ((w : ↥Q) : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hwo
      omega
    have hwZ := hcentZ _ (w : ↥Q).2 hw3 hw1 hwcent
    have hzw : zpowers ((w : ↥Q) : G) = zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwZ) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hwo,
        orderOf_eq_prime hyp.central.pow_eq_one hyp.central.ne_one]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hzw ▸ mem_zpowers z : z ∈ zpowers ((w : ↥Q) : G))
    intro g hg
    rw [← hk]
    exact (Commute.zpow_right (hwcent g hg) k)
  have hU1 : ∀ R : Subgroup G, R ≤ U → 1 ≤ CFSG.Open.pRank 3 R →
      normalizer (R : Set G) ⊓ H ≤ H ⊓ M := by
    intro R hRU hR1 g hg
    refine ⟨hg.2, ?_⟩
    obtain ⟨E, hER, -, hEc⟩ := exists_isElemAbelian_of_le_pRank Nat.prime_three hR1
    by_cases hRU' : R = U
    · subst hRU'
      exact normalizer_le_of_le_of_two_le_pRank hS hyp.u0 hsit'.mem_sigmaA
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
      exact P614CE.sit_normalizer_zpowers_le hsit (hQM (hUQ (hRU u.2))) hu1' hu3
        (hUr _ (hRU u.2) hu1') hg.1
  have hQ2 : ∀ R : Subgroup G, R ≤ Q → 2 ≤ CFSG.Open.pRank 3 R →
      normalizer (R : Set G) ⊓ H ≤ H ⊓ M := fun R hRQ hR2 g hg =>
    ⟨hg.2, normalizer_le_of_le_of_two_le_pRank hS hyp.u0 hsit'.mem_sigmaA
      hsit'.isCoreMaxLocal (hQp.to_le hRQ) (hRQ.trans hQM) hR2 hg.1⟩
  have hYH : H ⊓ M ≠ H := fun h => hyp.optimal.ext.pair.not_le (h ▸ inf_le_right)
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.kProper H
        (twoLocal_ne_top hS.nonab H hyp.optimal.ext.pair.isTwoLocal))
  obtain ⟨K, hKX, hKn, -, -, hKmax, hcov, hiso, -⟩ := k278 G H Q B U (H ⊓ M) hKH hH2 hQsyl
    (P614CE.isCyclic_center_of_pRank_le_two hH2.le hQH hQp hBQ hpl.isElemAbelian hpl.card_eq
      hqQ hq3 hqB)
    hBQ hpl.isElemAbelian (by rw [hpl.card_eq]; norm_num) hUQ hUe (by rw [hUc]; norm_num) hnc
    hwc inf_le_left hYH hU1 hQ2
  exact ⟨Q, K, hQsyl, hQM, hBQ, hQ27, hH2, hzc, hQ2, hKX, hKn, hKmax, hcov, hiso⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614DOG
