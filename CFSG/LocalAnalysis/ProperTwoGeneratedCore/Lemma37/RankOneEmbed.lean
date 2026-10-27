module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneKey

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

abbrev embedImage (H : Subgroup G) (z : G) (J : Subgroup (EscapingQuotient z)) :
    Subgroup (J ⧸ Subgroup.center J) :=
  ((escapingImage H z).subgroupOf J).map (QuotientGroup.mk' (Subgroup.center J))

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem sylow_quaternion {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L)
    (T : Sylow 2 L) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup L) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hrank := h.component_pRank_le_one hL
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide)] at hrank
  have hnot := LocalCriterionClassFreeAffine.not_twoRankAtLeastTwo_of_twoRank_le_one hrank
  rcases CFSG.BenderSuzuki.sylowTwo_cyclic_or_quaternion_of_not_twoRank hnot T with hcyc | hquat
  · exact absurd hcyc (not_isCyclic_sylow_two_of_commutator_eq_top
      hL.1.1.commutator_eq_top (two_dvd_card_of_isComponent hL) T)
  · exact hquat

theorem eq_of_mem_center {L : Subgroup (EscapingQuotient z)} (hL : CFSG.IsComponent L) {c : L}
    (hc : c ∈ Subgroup.center L) :
    (c : EscapingQuotient z) = 1 ∨ (c : EscapingQuotient z) = escapingBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ2, -⟩ := component_center_le_twoCore h.quotientData.oddCore_eq_bot hL
  have hcp : IsPGroup 2 (Subgroup.zpowers c) :=
    hZ2.to_le (Subgroup.zpowers_le.mpr hc)
  obtain ⟨T, hT⟩ := hcp.exists_le_sylow
  obtain ⟨r, hr, ⟨e⟩⟩ := h.sylow_quaternion hL T
  have hcT : c ∈ (T : Subgroup L) := hT (Subgroup.mem_zpowers c)
  have hcen : (⟨c, hcT⟩ : (T : Subgroup L)) ∈ Subgroup.center (T : Subgroup L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hc g)
  have hm : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 := orderOf_dvd_two_of_mem_center_quaternion hm e hcen
  rw [Subgroup.orderOf_mk, ← Subgroup.orderOf_coe] at h2
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact Or.inl (orderOf_eq_one_iff.mp h1)
  · exact Or.inr (h.eq_bar_of_mem_component hL c.2 h1)

theorem eq_of_mem_centralizer_component {L : Subgroup (EscapingQuotient z)}
    (hL : CFSG.IsComponent L) {x : EscapingQuotient z} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (L : Set (EscapingQuotient z))) :
    x = 1 ∨ x = escapingBar z := by
  refine h.eq_of_mem_center hL (c := ⟨x, hxL⟩) ?_
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)

theorem bar_sq : escapingBar z ^ 2 = 1 := by
  have := pow_orderOf_eq_one (escapingBar z)
  rwa [h.quotientData.bar_order] at this

theorem bar_ne_one : escapingBar z ≠ 1 := fun h1 => by
  have := h.quotientData.bar_order
  rw [h1, orderOf_one] at this
  exact absurd this (by decide)

theorem ne_of_sq_eq_bar {t : EscapingQuotient z} (ht : t ^ 2 = escapingBar z) :
    t ≠ 1 ∧ t ≠ escapingBar z := by
  refine ⟨fun h1 => h.bar_ne_one ?_, fun h1 => h.bar_ne_one ?_⟩
  · rw [← ht, h1, one_pow]
  · rw [← ht, h1, h.bar_sq]

theorem mem_image_of_conj_eq
    {t c : EscapingQuotient z} (htJ : t ∈ J)
    (htH : t ∈ escapingImage H z) (ht2 : t ^ 2 = escapingBar z) (hcJ : c ∈ J)
    (hc : c⁻¹ * t * c = t ∨ c⁻¹ * t * c = t * escapingBar z) : c ∈ escapingImage H z := by
  have hq := h.quotientData
  obtain ⟨k, hkS, hkC, hk2⟩ := h.exists_key
  have hkt : Commute k t := (Subgroup.mem_centralizer_iff.mp hkC t htJ).symm
  have hkc : Commute k c := (Subgroup.mem_centralizer_iff.mp hkC c hcJ).symm
  have he2 : (k * t) ^ 2 = 1 := by
    rw [hkt.mul_pow, hk2, ht2, ← pow_two, h.bar_sq]
  have htC : t ∉ Subgroup.centralizer (J : Set (EscapingQuotient z)) := fun htC => by
    obtain ⟨h1, h2⟩ := h.ne_of_sq_eq_bar ht2
    rcases h.eq_of_mem_centralizer_component h.component htJ htC with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hkinv : k⁻¹ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.inv_mem _ hkC
  have he1 : k * t ≠ 1 := fun h1 => htC (by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact hkinv)
  have hez : k * t ≠ escapingBar z := fun h1 => htC (by
    rw [show t = k⁻¹ * escapingBar z by rw [← h1, inv_mul_cancel_left]]
    exact Subgroup.mul_mem _ hkinv h.quotientData.bar_mem_component_centralizer)
  have heH : k * t ∈ escapingImage H z :=
    (escapingImage H z).mul_mem (h.sylowImage_le hkS) htH
  refine hq.mem_image_of_conj_mem heH (orderOf_eq_prime he2 he1) hez ?_
  have hck : c⁻¹ * (k * t) * c = k * (c⁻¹ * t * c) := by
    have hck' : c⁻¹ * k = k * c⁻¹ := (hkc.inv_right).eq.symm
    calc c⁻¹ * (k * t) * c = (c⁻¹ * k) * t * c := by group
      _ = (k * c⁻¹) * t * c := by rw [hck']
      _ = k * (c⁻¹ * t * c) := by group
  rw [hck]
  rcases hc with hc | hc
  · rw [hc]
    exact heH
  · rw [hc, ← mul_assoc]
    exact (escapingImage H z).mul_mem heH hq.bar_mem_image

theorem mem_image_of_mem_normalizer
    {n : EscapingQuotient z} (hnJ : n ∈ J)
    (hn : n ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) : Set (EscapingQuotient z))) :
    n ∈ escapingImage H z := by
  have hq := h.quotientData
  obtain ⟨k, hkS, hkC, hk2⟩ := h.exists_key
  obtain ⟨a, haS, haJ, ha2⟩ := h.exists_sq_eq_bar h.component
  set W := Subgroup.zpowers k ⊔ (escapingSylowImage S z ⊓ J) with hW
  have hWH : W ≤ escapingImage H z :=
    sup_le (Subgroup.zpowers_le.mpr (h.sylowImage_le hkS)) (inf_le_left.trans h.sylowImage_le)
  have hka : Commute k a := (Subgroup.mem_centralizer_iff.mp hkC a haJ).symm
  have hkaW : k * a ∈ W :=
    W.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers k)) (Subgroup.mem_sup_right ⟨haS, haJ⟩)
  have hzW : escapingBar z ∈ W := by
    rw [← ha2]
    exact W.pow_mem (Subgroup.mem_sup_right ⟨haS, haJ⟩) 2
  have hka2 : (k * a) ^ 2 = 1 := by rw [hka.mul_pow, hk2, ha2, ← pow_two, h.bar_sq]
  have haC : a ∉ Subgroup.centralizer (J : Set (EscapingQuotient z)) := fun haC => by
    obtain ⟨h1, h2⟩ := h.ne_of_sq_eq_bar ha2
    rcases h.eq_of_mem_centralizer_component h.component haJ haC with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hkinv : k⁻¹ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    Subgroup.inv_mem _ hkC
  have hka1 : k * a ≠ 1 := fun h1 => haC (by
    rw [eq_inv_of_mul_eq_one_right h1]
    exact hkinv)
  have hkaz : k * a ≠ escapingBar z := fun h1 => haC (by
    rw [show a = k⁻¹ * escapingBar z by rw [← h1, inv_mul_cancel_left]]
    exact Subgroup.mul_mem _ hkinv h.quotientData.bar_mem_component_centralizer)
  have hrank : 2 ≤ CFSG.Open.pRank 2 W :=
    two_le_pRank_of_commuting_involutions hkaW hzW (orderOf_eq_prime hka2 hka1) hq.bar_order hkaz
      (hq.commute_bar _)
  have hnk : n ∈ Subgroup.normalizer ((Subgroup.zpowers k : Subgroup _) : Set (EscapingQuotient z))
      := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left
      (show Commute k n from (Subgroup.mem_centralizer_iff.mp hkC n hnJ).symm) i).eq
  exact hq.normalizer_le W hWH hrank
    (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hnk, hn⟩)

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
