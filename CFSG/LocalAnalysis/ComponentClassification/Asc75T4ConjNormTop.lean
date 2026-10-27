module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Top

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

theorem normalIn_twoPrimeLayerIn_of_normalIn {A D M : Subgroup G} (hA : TightlyEmbedded A)
    (h4 : HasFourGroup (twoPrimeLayerIn A)) (hKD : NormalIn (twoPrimeLayerIn A) D)
    (hDM : NormalIn D M) : NormalIn (twoPrimeLayerIn A) (twoPrimeLayerIn M) := by
  set K := twoPrimeLayerIn A with hKdef
  have hKM : K ≤ M := hKD.1.trans hDM.1
  have hON : M ≤ normalizer (oddCoreIn M : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn M)
  have hinf : K ⊓ oddCoreIn M = oddCoreIn K := by
    refine le_antisymm (le_oddCoreIn (normalIn_of_le_normalizer inf_le_left ?_)
      ((odd_card_oddCoreIn _).of_dvd_nat (card_dvd_of_le inf_le_right))) ?_
    · exact (le_inf le_normalizer (hKM.trans hON)).trans (inf_normalizer_le_normalizer_inf _ _)
    · exact le_inf (oddCoreIn_le K)
        ((oddCoreIn_le_of_normalIn hKD).trans (oddCoreIn_le_of_normalIn hDM))
  have hKsub : (quotImage M K).IsSubnormal :=
    isSubnormal_quotImage_of_subgroupOf (isSubnormal_subgroupOf_of_normalIn hKD hDM)
  have hKlay : CFSG.layer (quotImage M K) = ⊤ :=
    layer_map_mk_eq_top hKM hinf (isSemisimpleQ_twoPrimeLayerIn A)
  have hKle : K ≤ twoPrimeLayerIn M := by
    have h := map_subtype_layer_le_layer_of_isSubnormal hKsub
    rw [hKlay, ← MonoidHom.range_eq_map, range_subtype] at h
    intro k hk
    exact mem_twoPrimeLayerIn_iff.mpr ⟨hKM hk, h ⟨⟨k, hKM hk⟩, hk, rfl⟩⟩
  have hEN : CFSG.layer (↥M ⧸ CFSG.Assembly.oddCore ↥M) ≤
      normalizer (quotImage M K : Set (↥M ⧸ CFSG.Assembly.oddCore ↥M)) := by
    refine sSup_le fun C hC => ?_
    rcases CFSG.LocalCores.component_subnormal_subgroup hC hKsub with h | h
    · exact h.trans le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans (centralizer_le_normalizer _)
  have hOA : oddCoreIn M ≤ normalizer (A : Set G) :=
    oddCoreIn_le_normalizer hA (twoPrimeLayerIn_le A) hKM h4
  obtain ⟨E, hEK, hE, hE4⟩ := h4
  have hEne : E ≠ ⊥ := fun h => by rw [h, card_bot] at hE4; norm_num at hE4
  obtain ⟨⟨u, huE⟩, hu1⟩ := ne_bot_iff_exists_ne_one.mp hEne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huK := hEK huE
  have hLA : twoPrimeLayerIn M ≤ normalizer (A : Set G) := by
    intro x hx
    obtain ⟨hxM, hxE⟩ := mem_twoPrimeLayerIn_iff.mp hx
    have hxN := hEN hxE
    have hm : QuotientGroup.mk' (CFSG.Assembly.oddCore M)
        (⟨x, hxM⟩ * ⟨u, hKM huK⟩ * ⟨x, hxM⟩⁻¹) ∈ quotImage M K := by
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hxN _).mp ⟨⟨u, hKM huK⟩, huK, rfl⟩
    have hv : x * u * x⁻¹ ∈ K ⊔ oddCoreIn M := mem_sup_oddCoreIn_of_mk_mem hm
    have hv2 : (x * u * x⁻¹) ^ 2 ^ 1 = 1 := by
      rw [pow_one, conj_pow, hE u huE, mul_one, mul_inv_cancel]
    have hvA : x * u * x⁻¹ ∈ A := mem_of_two_element_of_le_sup (twoPrimeLayerIn_le A)
      (odd_card_oddCoreIn _) (hKM.trans hON) hOA hv hv2
    have hvAx : x * u * x⁻¹ ∈ rightConjugate A x⁻¹ := by
      rw [mem_rightConjugate_iff, show x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u by group]
      exact twoPrimeLayerIn_le A huK
    have hv1 : x * u * x⁻¹ ≠ 1 := by
      intro h
      apply hu1'
      rw [show u = x⁻¹ * (x * u * x⁻¹) * x by group, h]
      group
    have heven : Even (Nat.card (A ⊓ rightConjugate A x⁻¹ : Subgroup G)) := by
      have hz : Nat.card (zpowers (x * u * x⁻¹)) = 2 := by
        rw [Nat.card_zpowers, orderOf_eq_prime (by simpa using hv2) hv1]
      exact even_iff_two_dvd.mpr (hz ▸ card_dvd_of_le ((zpowers_le).mpr ⟨hvA, hvAx⟩))
    exact inv_mem_iff.mp (mem_normalizer_of_even_inf hA heven)
  exact normalIn_of_le_normalizer hKle (hLA.trans (normalizer_le_normalizer_twoPrimeLayerIn A))

end CFSG.ComponentClassification.Asc75T4
