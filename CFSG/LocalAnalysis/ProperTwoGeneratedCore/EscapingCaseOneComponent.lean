module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictions
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedComponentStructure
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section General

variable {X : Type} [Group X] [Finite X]

theorem exists_commuting_involutions_of_two_le_pRank {X : Type*} [Group X] [Finite X]
    {K : Subgroup X}
    (hK : 2 ≤ CFSG.Open.pRank 2 K) :
    ∃ a ∈ K, ∃ b ∈ K, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ Commute a b := by
  obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by decide : 1 < 2) K
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 K := Nat.pow_le_pow_right (by norm_num) hK
  have hnt : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨⟨a, haE⟩, ha1⟩ := exists_ne (1 : E)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hE.2 a haE) ha1'
  obtain ⟨b, hbE, hba⟩ : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers a from hall)
    rw [Nat.card_zpowers, ha2] at hle
    omega
  have hb1 : b ≠ 1 := fun h => hba (h ▸ Subgroup.one_mem _)
  refine ⟨a, hEK haE, b, hEK hbE, ha2, orderOf_eq_prime (hE.2 b hbE) hb1,
    fun h => hba (h ▸ Subgroup.mem_zpowers a), ?_⟩
  exact congrArg Subtype.val (@mul_comm' E _ hE.1 ⟨a, haE⟩ ⟨b, hbE⟩)

theorem eq_of_mem_twoCore_of_rank_one {t : X} (htc : t ∈ Subgroup.center X)
    (ht : orderOf t = 2) (htO : t ∈ pCore 2 X) (hrank : CFSG.Open.pRank 2 (pCore 2 X) = 1)
    {w : X} (hw : w ∈ pCore 2 X) (hw2 : orderOf w = 2) : w = t := by
  by_contra hne
  have h := two_le_pRank_of_commuting_involutions hw htO hw2 ht hne
    (Subgroup.mem_center_iff.mp htc w)
  omega

theorem component_center_le_twoCore (hodd : pPrimeCore 2 X = ⊥) {J : Subgroup X}
    (hJ : CFSG.IsComponent J) :
    IsPGroup 2 (Subgroup.center J) ∧ (Subgroup.center J).map J.subtype ≤ pCore 2 X := by
  have hJ' := (CFSG.isComponent_iff_open J).mp hJ
  have hcoreJ := cfsg_subnormal_primeComplementCore_eq_bot 2 J hJ'.2.1 hodd
  have hZ := trivial_primeComplementCore_center_le_pCore 2 Nat.prime_two hcoreJ
  have hsub := cfsg_subnormal_pCoreOf_le 2 hJ'.2.1
  rw [pCoreOf_top_eq_pCore] at hsub
  exact ⟨(CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2).to_le hZ,
    (Subgroup.map_mono hZ).trans hsub⟩

variable (hodd : pPrimeCore 2 X = ⊥) {t : X} (htc : t ∈ Subgroup.center X)
  (ht : orderOf t = 2) (htO : t ∈ pCore 2 X) (hrank : CFSG.Open.pRank 2 (pCore 2 X) = 1)
  {J : Subgroup X} (hJ : CFSG.IsComponent J) (htJ : t ∉ J)
include hodd htc ht htO hrank hJ htJ

theorem component_center_eq_bot_of_not_mem : Subgroup.center J = ⊥ := by
  obtain ⟨h2, hle⟩ := component_center_le_twoCore hodd hJ
  by_contra hne
  have hnt : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  have hwX : (((w : J) : X)) ∈ pCore 2 X := hle (Subgroup.mem_map_of_mem _ w.property)
  have hw2 : orderOf ((w : J) : X) = 2 := by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have heq := eq_of_mem_twoCore_of_rank_one htc ht htO hrank hwX hw2
  exact htJ (heq ▸ (w : J).property)

theorem component_isSimpleGroup_of_not_mem : IsSimpleGroup J := by
  have hcenter := component_center_eq_bot_of_not_mem hodd htc ht htO hrank hJ htJ
  let projection := QuotientGroup.mk' (Subgroup.center J)
  have hkernel : projection.ker = ⊥ := by rw [QuotientGroup.ker_mk', hcenter]
  let equivalence := MulEquiv.ofBijective projection
    ⟨(MonoidHom.ker_eq_bot_iff projection).mp hkernel, QuotientGroup.mk'_surjective _⟩
  let : IsSimpleGroup (J ⧸ Subgroup.center J) := hJ.1.2.1
  exact equivalence.isSimpleGroup

theorem component_two_le_pRank_of_not_mem : 2 ≤ CFSG.Open.pRank 2 J := by
  have hcenter := component_center_eq_bot_of_not_mem hodd htc ht htO hrank hJ htJ
  have h := CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hJ.1
    (by rw [hcenter, Subgroup.card_bot]; exact odd_one)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  rwa [pRank_subgroup_eq_internal_top 2 (by decide) J]

end General

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {x : G}

namespace EscapingQuotientData

variable (hq : EscapingQuotientData H x) {J : Subgroup (EscapingQuotient x)}
  (hJ : CFSG.IsComponent J) (hxJ : escapingBar x ∉ J)
include hq hJ hxJ

theorem component_center_eq_bot : Subgroup.center J = ⊥ :=
  component_center_eq_bot_of_not_mem hq.oddCore_eq_bot hq.bar_mem_center hq.bar_order
    hq.bar_mem_twoCore hq.twoCore_rank hJ hxJ

theorem component_isSimpleGroup : IsSimpleGroup J :=
  component_isSimpleGroup_of_not_mem hq.oddCore_eq_bot hq.bar_mem_center hq.bar_order
    hq.bar_mem_twoCore hq.twoCore_rank hJ hxJ

theorem component_two_le_pRank : 2 ≤ CFSG.Open.pRank 2 J :=
  component_two_le_pRank_of_not_mem hq.oddCore_eq_bot hq.bar_mem_center hq.bar_order
    hq.bar_mem_twoCore hq.twoCore_rank hJ hxJ

theorem component_characteristic : J.Characteristic := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  exact proper_full_core_high_rank_component_characteristic U _ hq.image_ne_top hUH hcore J
    ((CFSG.isComponent_iff_open J).mp hJ) (hq.component_two_le_pRank hJ hxJ)

theorem component_normal : J.Normal := by
  have := hq.component_characteristic hJ hxJ
  infer_instance

theorem component_unique {L : Subgroup (EscapingQuotient x)} (hL : CFSG.IsComponent L)
    (hLrank : 2 ≤ CFSG.Open.pRank 2 L) : L = J := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  exact proper_full_core_high_rank_component_unique U _ hq.image_ne_top hUH hcore L J
    ((CFSG.isComponent_iff_open L).mp hL) ((CFSG.isComponent_iff_open J).mp hJ) hLrank
    (hq.component_two_le_pRank hJ hxJ)

theorem component_not_le_image : ¬ J ≤ escapingImage H x := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  have := hq.component_normal hJ hxJ
  exact normal_rank_two_not_le_overgroup U _ hq.image_ne_top hUH hcore J
    (hq.component_two_le_pRank hJ hxJ)

theorem component_centralizer_pRank_le_one :
    CFSG.Open.pRank 2 (Subgroup.centralizer (J : Set (EscapingQuotient x))) ≤ 1 := by
  obtain ⟨U, hUH, hcore⟩ := hq.sylow
  have := hq.component_normal hJ hxJ
  exact normal_rank_two_centralizer_rank_le_one U _ hq.image_ne_top hUH hcore J
    (hq.component_two_le_pRank hJ hxJ)

omit hJ hxJ in
theorem bar_mem_component_centralizer :
    escapingBar x ∈ Subgroup.centralizer (J : Set (EscapingQuotient x)) :=
  Subgroup.mem_centralizer_iff.mpr fun y _ => (hq.commute_bar y).eq

theorem eq_bar_of_mem_component_centralizer {k : EscapingQuotient x}
    (hk : k ∈ Subgroup.centralizer (J : Set (EscapingQuotient x))) (hk2 : orderOf k = 2) :
    k = escapingBar x := by
  by_contra hne
  have h := two_le_pRank_of_commuting_involutions hk hq.bar_mem_component_centralizer
    hk2 hq.bar_order hne (hq.commute_bar k)
  have := hq.component_centralizer_pRank_le_one hJ hxJ
  omega

theorem component_inf_centralizer_eq_bot :
    J ⊓ Subgroup.centralizer (J : Set (EscapingQuotient x)) = ⊥ := by
  have hcenter := hq.component_center_eq_bot hJ hxJ
  refine le_bot_iff.mp fun y hy => ?_
  have hmem : (⟨y, hy.1⟩ : J) ∈ Subgroup.center J := Subgroup.mem_center_iff.mpr fun a =>
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp hy.2) a a.property)
  rw [hcenter, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

end EscapingQuotientData

end CFSG.ProperTwoGeneratedCore.Assembly
