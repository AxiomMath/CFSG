module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Class
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Tools

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem map_subtype_layer_le_layer_of_isSubnormal {A : Type*} [Group A] [Finite A]
    {M : Subgroup A} (hM : M.IsSubnormal) : (CFSG.layer M).map M.subtype ≤ CFSG.layer A := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← map_le_iff_le_comap]
  refine le_sSup (show CFSG.IsComponent (L.map M.subtype) from ⟨?_, hL.2.trans' hM⟩)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective M.subtype M.subtype_injective) hL.1

namespace MainSetting

variable {Q : Subgroup G} (hS : MainSetting Q)
include hS

theorem thm4Case1_of_normalizer_eq_top (hND : normalizer (linkedLayer Q : Set G) = ⊤) :
    Thm4Case1 Q := by
  set K := twoPrimeLayerIn Q
  set D := linkedLayer Q
  have hKD : NormalIn K D := hS.normalIn_linkedLayer (self_mem_linkedClass Q)
  have hDG : NormalIn D ⊤ := normalIn_of_le_normalizer le_top (by rw [hND])
  have hinf : K ⊓ oddCoreIn (⊤ : Subgroup G) = oddCoreIn K := by
    refine le_antisymm (le_oddCoreIn (normalIn_of_le_normalizer inf_le_left ?_)
      ((odd_card_oddCoreIn _).of_dvd_nat (card_dvd_of_le inf_le_right))) ?_
    · exact (le_inf le_normalizer (le_top.trans
        (normalIn_le_normalizer (oddCoreIn_normalIn ⊤)))).trans
        (inf_normalizer_le_normalizer_inf _ _)
    · exact le_inf (oddCoreIn_le K)
        ((oddCoreIn_le_of_normalIn hKD).trans (oddCoreIn_le_of_normalIn hDG))
  have hKsub : (quotImage ⊤ K).IsSubnormal :=
    isSubnormal_quotImage_of_subgroupOf (isSubnormal_subgroupOf_of_normalIn hKD hDG)
  have hKlay : CFSG.layer (quotImage ⊤ K) = ⊤ :=
    layer_map_mk_eq_top le_top hinf (isSemisimpleQ_twoPrimeLayerIn Q)
  have hKle : K ≤ twoPrimeLayerIn (⊤ : Subgroup G) := by
    have h := map_subtype_layer_le_layer_of_isSubnormal hKsub
    rw [hKlay, ← MonoidHom.range_eq_map, range_subtype] at h
    intro k hk
    exact mem_twoPrimeLayerIn_iff.mpr ⟨mem_top k, h ⟨⟨k, mem_top k⟩, hk, rfl⟩⟩
  have hEN : CFSG.layer (↥(⊤ : Subgroup G) ⧸ CFSG.Assembly.oddCore ↥(⊤ : Subgroup G)) ≤
      normalizer (quotImage ⊤ K :
        Set (↥(⊤ : Subgroup G) ⧸ CFSG.Assembly.oddCore ↥(⊤ : Subgroup G))) := by
    refine sSup_le fun C hC => ?_
    rcases CFSG.LocalCores.component_subnormal_subgroup hC hKsub with h | h
    · exact h.trans le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le_normalizer _)
  have hOQ : oddCoreIn (⊤ : Subgroup G) ≤ normalizer (Q : Set G) :=
    oddCoreIn_le_normalizer hS.tight (twoPrimeLayerIn_le Q) le_top hS.four
  have hON : (⊤ : Subgroup G) ≤ normalizer (oddCoreIn (⊤ : Subgroup G) : Set G) :=
    normalIn_le_normalizer (oddCoreIn_normalIn ⊤)
  obtain ⟨E, hEK, hE, hE4⟩ := hS.four
  have hEne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨u, huE⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huK := hEK huE
  have hLQ : twoPrimeLayerIn (⊤ : Subgroup G) ≤ normalizer (Q : Set G) := by
    intro x hx
    obtain ⟨hxt, hxE⟩ := mem_twoPrimeLayerIn_iff.mp hx
    have hxN := hEN hxE
    have hm : QuotientGroup.mk' (CFSG.Assembly.oddCore (⊤ : Subgroup G))
        (⟨x, hxt⟩ * ⟨u, mem_top u⟩ * ⟨x, hxt⟩⁻¹) ∈ quotImage ⊤ K := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hxN _).mp ⟨⟨u, mem_top u⟩, huK, rfl⟩
    have hv : x * u * x⁻¹ ∈ K ⊔ oddCoreIn (⊤ : Subgroup G) := mem_sup_oddCoreIn_of_mk_mem hm
    have hv2 : (x * u * x⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, conj_pow, hE u huE, mul_one, mul_inv_cancel]
    have hvQ : x * u * x⁻¹ ∈ Q := mem_of_two_element_of_le_sup (twoPrimeLayerIn_le Q)
      (odd_card_oddCoreIn _) (le_top.trans hON) hOQ hv hv2
    have hvQx : x * u * x⁻¹ ∈ rightConjugate Q x⁻¹ := by
      rw [mem_rightConjugate_iff, show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group]
      exact twoPrimeLayerIn_le Q huK
    have hv1 : x * u * x⁻¹ ≠ 1 := by
      intro h
      apply hu1'
      rw [show u = x⁻¹ * (x * u * x⁻¹) * x by group, h]
      group
    have heven : Even (Nat.card (Q ⊓ rightConjugate Q x⁻¹ : Subgroup G)) := by
      have hz : Nat.card (zpowers (x * u * x⁻¹)) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (by simpa using hv2) hv1]
      exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hvQ, hvQx⟩))
    exact inv_mem_iff.mp (mem_normalizer_of_even_inf hS.tight heven)
  exact normalIn_of_le_normalizer hKle (hLQ.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))

end MainSetting

end CFSG.ComponentClassification.Asc75T4
