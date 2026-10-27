module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionCoverage

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

universe u

variable {G : Type u} [Group G] [Finite G]

theorem exists_conj_mem_of_index_modEq_two (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2)
    (J : Subgroup G) (hJ : J.index ≡ 2 [MOD 4]) (t : G) (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ J := by
  have hJ' : J.index % 4 = 2 := hJ
  by_contra hnone
  have hmiss : ∀ g : G, g⁻¹ * t * g ∉ J := fun g hg => hnone ⟨g, hg⟩
  obtain ⟨sign, -, -, hsign, -⟩ := coset_involution_sign_obstruction J (J.index / 2)
    (Nat.odd_iff.mpr (by omega)) (by omega) (by omega) t ht hmiss
  exact hindexTwo _ hsign

theorem exists_conj_mem_of_sylow_relIndex_two (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2)
    (S : Sylow 2 G) (J : Subgroup G) (hJS : J ≤ S) (hJ : J.relIndex S = 2) (t : G)
    (ht : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ J := by
  refine exists_conj_mem_of_index_modEq_two hindexTwo J ?_ t ht
  have hodd : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
  change J.index % 4 = 2 % 4
  rw [← Subgroup.relIndex_mul_index hJS, hJ]
  omega

theorem index_two_mod_four_subgroups_meet_involution_classes
    (hindexTwo : ∀ K : Subgroup G, K.index ≠ 2) :
    (∀ J : Subgroup G, J.index ≡ 2 [MOD 4] → ∀ t : G, orderOf t = 2 →
      ∃ g : G, g⁻¹ * t * g ∈ J) ∧
    ∀ (S : Sylow 2 G) (J : Subgroup G), J ≤ S → J.relIndex S = 2 → ∀ t : G, orderOf t = 2 →
      ∃ g : G, g⁻¹ * t * g ∈ J :=
  ⟨fun J hJ t ht => exists_conj_mem_of_index_modEq_two hindexTwo J hJ t ht,
    fun S J hJS hJ t ht => exists_conj_mem_of_sylow_relIndex_two hindexTwo S J hJS hJ t ht⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
