module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepBAction
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632StepBNum
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632WreathRec

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem stepB_card_dvd_eighty_one (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z g : G} {T : Subgroup G}
    (hd : SmallRank3Data P M x z g T) : Nat.card (P : Subgroup G) ∣ 81 := by
  obtain ⟨V, _, _, ρ, hV, hV2, hρ, hfree, hnear⟩ := exists_faithful_two_group_action hS hs hd
  obtain ⟨b, hb, hgx⟩ := hd.g_act
  have hzc : ∀ a : (P : Subgroup G), a * ⟨z, hd.central.mem⟩ = ⟨z, hd.central.mem⟩ * a :=
    fun a => Subtype.ext (mem_centralizer_iff.mp hd.central.centralizes a a.2)
  exact card_dvd_eighty_one_of_fixed_data P.isPGroup' ρ hV hV2 hρ (g := ⟨g, hd.g_mem⟩)
    (Subtype.ext hd.point.pow_eq_one) (Subtype.ext hd.central.pow_eq_one) hzc
    (hzc ⟨x, hd.point.mem⟩) hb (Subtype.ext hgx) hfree hnear

private theorem stepB_card_eq_eighty_one (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z g : G} {T : Subgroup G}
    (hd : SmallRank3Data P M x z g T) {E : Subgroup G} (hEP : E ≤ (P : Subgroup G))
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 27) : Nat.card (P : Subgroup G) = 81 := by
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hs.largeObstruction_empty x ⟨hPM hd.point.mem, hd.point.ne_one, hd.point.pow_eq_one,
      by omega, hd.point.not_centralizer_le⟩
  obtain ⟨m, hm⟩ : 27 ∣ Nat.card (P : Subgroup G) := hEc ▸ Subgroup.card_dvd_of_le hEP
  have hm3 : m ∣ 3 := by
    have h := stepB_card_dvd_eighty_one hS hs hd
    rw [hm, show (81 : ℕ) = 27 * 3 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with rfl | rfl
  ·
    exfalso
    have hEeq : E = (P : Subgroup G) := Subgroup.eq_of_le_of_card_ge hEP (by rw [hm, hEc])
    have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) := by
      intro a ha
      rw [mem_centralizer_singleton_iff]
      have := hE.1
      have hxE : x ∈ E := hEeq ▸ hd.point.mem
      have haE : a ∈ E := hEeq ▸ ha
      exact congrArg Subtype.val (mul_comm' (⟨a, haE⟩ : E) ⟨x, hxE⟩)
    have := pRank_mono 3 (by norm_num) hPC
    omega
  · rw [hm]

theorem nonempty_mulEquiv_wreath_of_data (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z g : G} {T : Subgroup G}
    (hd : SmallRank3Data P M x z g T) :
    Nonempty ((P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hs.mem_sigmaA hs.isCoreMaxLocal
  have hplane := SmallRankPlane.of_situation hS hs hd.point hd.central
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained 3 (P : Subgroup G) (by omega)
  rw [hP3] at hEc
  norm_num at hEc
  have h81 := stepB_card_eq_eighty_one hS hs hd hEP hE hEc
  have hE' : IsElemAbelian 3 (E.subgroupOf (P : Subgroup G)) := by
    have := hE.1
    refine ⟨inferInstance, fun y hy => Subtype.ext ?_⟩
    exact hE.2 y (mem_subgroupOf.mp hy)
  have hEc' : Nat.card (E.subgroupOf (P : Subgroup G)) = 27 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hEP).toEquiv, hEc]
  set z' : (P : Subgroup G) := ⟨z, hd.central.mem⟩ with hz'
  have hzc : z' ∈ center (P : Subgroup G) := mem_center_iff.mpr fun a =>
    Subtype.ext (mem_centralizer_iff.mp hd.central.centralizes a a.2)
  have hz3 : orderOf z' = 3 := orderOf_eq_prime (Subtype.ext hd.central.pow_eq_one)
    fun h => hd.central.ne_one (congrArg Subtype.val h)
  have hZ : ∀ w ∈ center (P : Subgroup G), w ^ 3 = 1 → w ∈ zpowers z' := by
    intro w hw hw3
    have hwC : (w : G) ∈ centralizer ((P : Subgroup G) : Set G) := mem_centralizer_iff.mpr
      fun a ha => congrArg Subtype.val (mem_center_iff.mp hw ⟨a, ha⟩)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp
      (hplane.center (w : G) w.2 hwC (congrArg Subtype.val hw3))
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
  exact nonempty_mulEquiv_wreath_of_card_eq_eighty_one h81 hE' hEc' hzc hz3 hZ

end CFSG.LocalAnalysis.RankThreeTheoremC
