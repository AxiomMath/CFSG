module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.NonSquareCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderRoute
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralCentralizerBenderFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.GH74.Bender

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly CFSG.ProperTwoGeneratedCore.TheoremC

section Steps

variable {G : Type} [Group G] [Finite G]

theorem isConj_or_isConj_mul_escapingBar {H : Subgroup G} {x : G}
    (hq : EscapingQuotientData H x) (hsq : ∀ w : EscapingQuotient x, w ^ 2 ≠ escapingBar x)
    {a b : EscapingQuotient x} (ha : orderOf a = 2) (hax : a ≠ escapingBar x)
    (hb : orderOf b = 2) (hbx : b ≠ escapingBar x) :
    IsConj a b ∨ IsConj a (b * escapingBar x) := by
  obtain ⟨g, hg⟩ := (hq.benderImage_isStronglyEmbedded hsq).involutions_conjugate
    (isInvolution_benderMk hq.order ha hax) (isInvolution_benderMk hq.order hb hbx)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have h : (c⁻¹ * a * c)⁻¹ * b ∈ Subgroup.zpowers (escapingBar x) := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hg
  rcases Assembly.eq_one_or_eq_of_mem_zpowers hq.bar_order h with h1 | h1
  · rw [inv_mul_eq_one] at h1
    exact Or.inl (isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv, h1]⟩)
  · have hb' : b = c⁻¹ * a * c * escapingBar x := by rw [← h1, mul_inv_cancel_left]
    refine Or.inr (isConj_iff.mpr ⟨c⁻¹, ?_⟩)
    rw [hb', mul_assoc (c⁻¹ * a * c), escapingBar_mul_self hq.order, mul_one, inv_inv]

theorem exists_mk_eq_of_orderOf_sq_eq_two {S : Sylow 2 G} {z : G} {y : EscapingQuotient z}
    (hy : y ∈ escapingSylowImage S z) (hy2 : orderOf (y ^ 2) = 2) :
    ∃ x : Subgroup.centralizer ({z} : Set G), (x : G) ∈ (S : Subgroup G) ∧
      escapingMk z x = y ∧ orderOf (x ^ 2) = 2 := by
  obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp hy
  have hxS' : (x : G) ∈ (S : Subgroup G) := Subgroup.mem_subgroupOf.mp hxS
  refine ⟨x, hxS', rfl, orderOf_eq_prime ?_ fun h => ?_⟩
  · refine escapingMk_injOn_twoGroup S.isPGroup' ?_ (S : Subgroup G).one_mem ?_
    · simpa only [Subgroup.coe_pow] using
        (S : Subgroup G).pow_mem ((S : Subgroup G).pow_mem hxS' 2) 2
    · have h4 := pow_orderOf_eq_one (escapingMk z x ^ 2)
      rwa [hy2, ← map_pow, ← map_pow, ← map_one (escapingMk z)] at h4
  · rw [← map_pow, h, map_one, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)

theorem coreSetting_false_of_normal_component_mem
    {S : Sylow 2 G} {H : Subgroup G} {z : G}
    (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) (hsq : ∀ v ∈ (S : Subgroup G), v ^ 2 ≠ z)
    {J : Subgroup (EscapingQuotient z)} [J.Normal] (hJ : CFSG.IsComponent J)
    (hzJ : escapingBar z ∈ J) (hodd : Odd J.index)
    (hcenter : (Subgroup.center J).map J.subtype = Subgroup.zpowers (escapingBar z))
    (hB : fusionIsBenderGroup (J ⧸ Subgroup.center J)) : False := by
  have hq := escapingQuotientData hset (hset.sylow_le hz.1) hz.2.1 hesc
  have hsq' := centralInvolution_not_sq_bar hz hsq
  set Sbar : Sylow 2 (EscapingQuotient z) :=
    (S.subtype hz.le_centralizer).mapSurjective (QuotientGroup.mk'_surjective _)
  have hSbar : (Sbar : Subgroup (EscapingQuotient z)) = escapingSylowImage S z := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hSJ : (Sbar : Subgroup (EscapingQuotient z)) ≤ J :=
    le_of_normal_of_odd_index hodd Sbar.isPGroup'
  set Q : Sylow 2 J := Sbar.subtype hSJ with hQdef
  have hQmem : ∀ q : J, q ∈ (Q : Subgroup J) ↔
      (q : EscapingQuotient z) ∈ escapingSylowImage S z := by
    intro q
    rw [hQdef, Sylow.coe_subtype, Subgroup.mem_subgroupOf, hSbar]
  set u : J := ⟨escapingBar z, hzJ⟩ with hudef
  have hu : orderOf u = 2 := by
    rw [hudef, Subgroup.orderOf_mk]
    exact hq.bar_order
  have hZ : ∀ s : J, s ∈ Subgroup.center J ↔ s = 1 ∨ s = u := by
    intro s
    rw [← Subgroup.mem_map_iff_mem J.subtype_injective, hcenter, Subgroup.coe_subtype]
    constructor
    · intro h
      rcases Assembly.eq_one_or_eq_of_mem_zpowers hq.bar_order h with h1 | h1
      · exact Or.inl (Subtype.ext h1)
      · exact Or.inr (Subtype.ext h1)
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hBF := benderBorelFactsHold _ (CFSG.GH74.isBenderGroup_of_fusionIsBenderGroup hB)
    (Q.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)))
  rw [Sylow.coe_mapSurjective] at hBF
  have hQ : ¬ (Q : Subgroup J) ≤ Subgroup.center J := by
    intro hle
    have hrank : 2 ≤ CFSG.Open.pRank 2 (Sbar : Subgroup (EscapingQuotient z)) := by
      rw [CFSG.ProperTwoGeneratedCore.sylow_two_rank_eq]
      have := hq.rank
      omega
    obtain ⟨a, haS, b, hbS, ha, hb, hab, -⟩ := exists_commuting_involutions_of_two_le_pRank hrank
    have key : ∀ w ∈ (Sbar : Subgroup (EscapingQuotient z)), orderOf w = 2 →
        w = escapingBar z := by
      intro w hw hw2
      rcases (hZ ⟨w, hSJ hw⟩).mp (hle ((hQmem _).mpr (hSbar ▸ hw))) with h | h
      · rw [show w = 1 from congrArg Subtype.val h, orderOf_one] at hw2
        exact absurd hw2 (by norm_num)
      · exact congrArg Subtype.val h
    exact hab ((key a haS ha).trans (key b hbS hb).symm)
  obtain ⟨y, hyQ, hy2, q, -, hqy⟩ := exists_sq_conj_eq_mul_of_borelFacts
    hJ.1.1.commutator_eq_top hu hZ Q hBF
    (fun y _ h => hsq' y (by rw [← Subgroup.coe_pow, h])) hQ
  have ht2 : orderOf ((y : EscapingQuotient z) ^ 2) = 2 := by
    rw [← Subgroup.coe_pow, Subgroup.orderOf_coe, hy2]
  have htt : IsConj ((y : EscapingQuotient z) ^ 2) ((y : EscapingQuotient z) ^ 2 * escapingBar z) :=
    isConj_iff.mpr ⟨(q : EscapingQuotient z)⁻¹, by
      have h := congrArg Subtype.val hqy
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at h
      rw [inv_inv, h]⟩
  obtain ⟨v, hzv, hv2, hvbar⟩ := exists_isConj_mk_ne_bar hset.simple hset.nonabelian hz.2.1
  have hv2' : orderOf v = 2 := by rwa [← Subgroup.orderOf_coe]
  have hvt : IsConj (escapingMk z v) ((y : EscapingQuotient z) ^ 2) := by
    rcases isConj_or_isConj_mul_escapingBar hq hsq' (escaping_orderOf_mk z hv2') hvbar ht2
      (hsq' _) with h | h
    · exact h
    · exact h.trans htt.symm
  obtain ⟨x, hxS, hxy, hx2⟩ := exists_mk_eq_of_orderOf_sq_eq_two ((hQmem y).mp hyQ) ht2
  have hvx : IsConj v (x ^ 2) :=
    escaping_isConj_of_isConj_mk z hv2' hx2 (by rw [map_pow, hxy]; exact hvt)
  have hxz : IsConj ((x : G) ^ 2) z :=
    (hzv.trans (MonoidHom.map_isConj (Subgroup.centralizer ({z} : Set G)).subtype hvx)).symm
  obtain ⟨w, hwS, hw⟩ := centralInvolution_exists_sq_of_isConj_sq hz hxz hxS rfl
  exact hsq w hwS hw

end Steps

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly in
theorem coreSetting_exists_component_not_mem_of_not_sq
    {G : Type} [Group G] [Finite G]
    {S : Sylow 2 G} {H : Subgroup G} {z : G}
    (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
    (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsq : ∀ v ∈ (S : Subgroup G), v ^ 2 ≠ z) :
    ∃ J : Subgroup (EscapingQuotient z), CFSG.IsComponent J ∧ escapingBar z ∉ J := by
  rcases (coreSetting_bender_route hset hz hesc hsq).2 with
    ⟨J, hJ, hzJ, -⟩ | ⟨J, hJn, hJ, hzJ, hodd, -, hcenter, hB⟩
  · exact ⟨J, hJ, hzJ⟩
  · exact (coreSetting_false_of_normal_component_mem hset hz hesc hsq hJ hzJ hodd hcenter
      hB).elim

end CFSG.ProperTwoGeneratedCore.Lemma37
