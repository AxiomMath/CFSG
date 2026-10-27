module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneEmbed
public import CFSG.StronglyEmbedded
public import CFSG.Monster.B.Recog.GenericStrongEmbedding

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem center_le_subgroupOf : Subgroup.center J ≤ (escapingImage H z).subgroupOf J := by
  intro c hc
  rw [Subgroup.mem_subgroupOf]
  rcases h.eq_of_mem_center h.component hc with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact h.quotientData.bar_mem_image

theorem embedImage_ne_top : embedImage H z J ≠ ⊤ := by
  intro htop
  apply h.not_le
  intro j hj
  have h1 : (⟨j, hj⟩ : J) ∈ (embedImage H z J).comap (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [htop]
    trivial
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr h.center_le_subgroupOf]
    at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem bar_mem_center :
    (⟨escapingBar z, h.square.caseTwo J h.component⟩ : J) ∈ Subgroup.center J := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h.quotientData.commute_bar g).eq

theorem orderOf_mk_eq_two {t : J} (ht : (t : EscapingQuotient z) ^ 2 = escapingBar z) :
    orderOf (QuotientGroup.mk' (Subgroup.center J) t) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    convert h.bar_mem_center using 1
    exact Subtype.ext ht
  · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
    intro hc
    obtain ⟨h1, h2⟩ := h.ne_of_sq_eq_bar ht
    rcases h.eq_of_mem_center h.component hc with h3 | h3
    · exact h1 h3
    · exact h2 h3

theorem even_card_embedImage : Even (Nat.card (embedImage H z J)) := by
  obtain ⟨a, haS, haJ, ha2⟩ := h.exists_sq_eq_bar h.component
  have haB : QuotientGroup.mk' (Subgroup.center J) ⟨a, haJ⟩ ∈ embedImage H z J :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (h.sylowImage_le haS))
  have hord : orderOf (⟨_, haB⟩ : embedImage H z J) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.orderOf_mk_eq_two (t := ⟨a, haJ⟩) ha2
  have hdvd := orderOf_dvd_natCard (⟨_, haB⟩ : embedImage H z J)
  rw [hord] at hdvd
  exact even_iff_two_dvd.mpr hdvd

theorem sq_eq_bar_of_orderOf_mk {t : J}
    (ht : orderOf (QuotientGroup.mk' (Subgroup.center J) t) = 2) :
    (t : EscapingQuotient z) ^ 2 = escapingBar z := by
  have hsq : t ^ 2 ∈ Subgroup.center J := by
    have h1 := pow_orderOf_eq_one (QuotientGroup.mk' (Subgroup.center J) t)
    rw [ht] at h1
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact h1
  have hne : t ∉ Subgroup.center J := fun hc => by
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff t).mpr hc, orderOf_one] at ht
    exact absurd ht (by decide)
  rcases h.eq_of_mem_center h.component hsq with h1 | h1
  · exfalso
    have ht1 : (t : EscapingQuotient z) ≠ 1 := fun h2 => hne (by
      rw [show t = 1 from Subtype.ext h2]
      exact Subgroup.one_mem _)
    have h2 : orderOf (t : EscapingQuotient z) = 2 :=
      orderOf_eq_prime (by rw [← Subgroup.coe_pow]; exact h1) ht1
    have h3 := h.unique _ t.2 h2
    apply hne
    convert h.bar_mem_center using 1
    exact Subtype.ext h3
  · rw [← Subgroup.coe_pow]
    exact h1

theorem centralizer_le_embedImage
    {t : J ⧸ Subgroup.center J} (ht : t ∈ embedImage H z J)
    (ht2 : orderOf t = 2) : Subgroup.centralizer {t} ≤ embedImage H z J := by
  obtain ⟨t', ht'H, rfl⟩ := Subgroup.mem_map.mp ht
  have hsq := h.sq_eq_bar_of_orderOf_mk ht2
  intro c hc
  obtain ⟨c', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) c
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : t'⁻¹ * (c'⁻¹ * t' * c') ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, map_mul,
      map_mul, map_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  have hconj : (c' : EscapingQuotient z)⁻¹ * t' * c' = t' ∨
      (c' : EscapingQuotient z)⁻¹ * t' * c' = t' * escapingBar z := by
    rcases h.eq_of_mem_center h.component hc' with h1 | h1
    · left
      have h2 : ((t' : EscapingQuotient z))⁻¹ * ((c' : EscapingQuotient z)⁻¹ * t' * c') = 1 := by
        simpa using h1
      rw [inv_mul_eq_one] at h2
      exact h2.symm
    · right
      have h2 : ((t' : EscapingQuotient z))⁻¹ * ((c' : EscapingQuotient z)⁻¹ * t' * c') =
          escapingBar z := by simpa using h1
      rw [← h2, mul_inv_cancel_left]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr
    (h.mem_image_of_conj_eq t'.2 (Subgroup.mem_subgroupOf.mp ht'H) hsq c'.2 hconj))

theorem normalizer_le_embedImage
    (P : Sylow 2 J)
    (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J) :
    Subgroup.normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J)) ≤ embedImage H z J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro n hn
  obtain ⟨n', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) n
  have h1 : n' ∈ (Subgroup.normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective
      (Subgroup.center J)) : Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J))).comap
      (QuotientGroup.mk' (Subgroup.center J)) := hn
  obtain ⟨hZ2, -⟩ := component_center_le_twoCore h.quotientData.oddCore_eq_bot h.component
  have hZP : Subgroup.center J ≤ (P : Subgroup J) := hZ2.le_sylow_of_normal P
  rw [Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _),
    Sylow.coe_mapSurjective, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr hZP] at h1
  have h2 : (n' : EscapingQuotient z) ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
        Set (EscapingQuotient z)) := by
    rw [← hP]
    exact Subgroup.le_normalizer_map J.subtype (Subgroup.mem_map_of_mem _ h1)
  exact Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr (h.mem_image_of_mem_normalizer n'.2 h2))

theorem isStronglyEmbeddedOrder
    : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (embedImage H z J) := by
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  exact CFSG.Monster.B.Recog.isStronglyEmbeddedOrder_of_centralizer_le h.embedImage_ne_top
    h.even_card_embedImage (fun t ht ht2 => h.centralizer_le_embedImage ht ht2) _
    (h.normalizer_le_embedImage P hP)

theorem isBenderGroup
    : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J) := by
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := h.component.1.2.1
  exact CFSG.BenderSuzuki.bender_suzuki _ h.isStronglyEmbeddedOrder

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
