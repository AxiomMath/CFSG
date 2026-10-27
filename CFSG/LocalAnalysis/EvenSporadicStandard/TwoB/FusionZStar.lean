module

public import CFSG.Adapters.Involutions

public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup

theorem exists_conj_mem_sylow_ne {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (T : Sylow 2 G) {t : G} (htT : t ∈ (T : Subgroup G))
    (htc : ∀ s ∈ (T : Subgroup G), s * t = t * s) (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ (T : Subgroup G) ∧ g⁻¹ * t * g ≠ t := by
  by_contra hcon
  have hwc : ∀ g : G, g⁻¹ * ((⟨t, htT⟩ : (T : Subgroup G)) : G) * g ∈ (T : Subgroup G) →
      g⁻¹ * ((⟨t, htT⟩ : (T : Subgroup G)) : G) * g = ((⟨t, htT⟩ : (T : Subgroup G)) : G) :=
    fun g hg => by_contra fun hne => hcon ⟨g, hg, hne⟩
  have hzZ : (⟨t, htT⟩ : (T : Subgroup G)) ∈ center (T : Subgroup G) := by
    rw [mem_center_iff]
    intro s
    exact Subtype.ext (htc s s.2)
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  obtain ⟨hfac, -⟩ := CFSG.Adapters.glauberman_zStar T ⟨t, htT⟩ hzZ
    (by rw [Subgroup.orderOf_mk]; exact ht) hwc
  have hcore : CFSG.oddCore G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
    · exact h
    · exact absurd (h ▸ mem_top t) (CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two ht)
  have hcen : t ∈ center G := by
    rw [mem_center_iff]
    intro g
    obtain ⟨c, hc, k, hk, hgck⟩ := hfac g
    rw [hcore, mem_bot] at hk
    rw [hk, mul_one] at hgck
    rw [hgck]
    exact mem_centralizer_singleton_iff.1 hc
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact ht1 (mem_bot.1 (h ▸ hcen))
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

end CFSG.EvenSporadicStandard.TwoB
