module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbeddingLocal

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem stronglyEmbedded_sylow_even (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (sylow : Sylow 2 subgroup) :
    Even (Nat.card ↥(sylow : Subgroup subgroup)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply even_iff_two_dvd.mpr
  have hdiv : 2 ∣ Nat.card ↥(sylow : Subgroup subgroup) *
      (sylow : Subgroup subgroup).index := by
    rw [Subgroup.card_mul_index]
    exact even_iff_two_dvd.mp hstrong.2.1
  exact (Nat.prime_two.dvd_mul.mp hdiv).resolve_right sylow.not_dvd_index

theorem stronglyEmbedded_sylow_inheritance (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) (sylow : Sylow 2 subgroup) :
    ∃ ambient : Sylow 2 G,
      (sylow : Subgroup subgroup).map subgroup.subtype = (ambient : Subgroup G) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let smaller : Subgroup G := (sylow : Subgroup subgroup).map subgroup.subtype
  have heven : Even (Nat.card smaller) := by
    rw [← Nat.card_congr ((sylow : Subgroup subgroup).equivMapOfInjective
      subgroup.subtype subgroup.subtype_injective).toEquiv]
    exact stronglyEmbedded_sylow_even subgroup hstrong sylow
  obtain ⟨ambient, hcomap⟩ := sylow.exists_comap_subtype_eq
  have hmap : (subgroup.comap (ambient : Subgroup G).subtype).map
      (ambient : Subgroup G).subtype = smaller := by
    rw [Subgroup.map_comap_eq, Subgroup.subtype_range]
    change (ambient : Subgroup G) ⊓ subgroup =
      (sylow : Subgroup subgroup).map subgroup.subtype
    rw [← hcomap, Subgroup.map_comap_eq, Subgroup.subtype_range, inf_comm]
  let within : Subgroup (ambient : Subgroup G) :=
    subgroup.comap (ambient : Subgroup G).subtype
  have hnormalizer : Subgroup.normalizer (within : Set (ambient : Subgroup G)) =
      within := by
    apply le_antisymm
    · intro element hmem
      have hmapped := Subgroup.le_normalizer_map (ambient : Subgroup G).subtype
        (Subgroup.mem_map.mpr ⟨element, hmem, rfl⟩)
      change (element : G) ∈ Subgroup.normalizer
        (((within.map (ambient : Subgroup G).subtype) : Subgroup G) : Set G) at hmapped
      change (element : G) ∈ subgroup
      rw [show within.map (ambient : Subgroup G).subtype = smaller from hmap] at hmapped
      exact stronglyEmbedded_even_subgroup_normalizer_le subgroup hstrong smaller
        (Subgroup.map_subtype_le _) heven hmapped
    · exact Subgroup.le_normalizer
  have _ : Group.IsNilpotent (ambient : Subgroup G) := ambient.isPGroup'.isNilpotent
  have htop : within = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent within hnormalizer
  have hambient_le : (ambient : Subgroup G) ≤ subgroup := by
    intro element hmem
    have hwithin : (⟨element, hmem⟩ : (ambient : Subgroup G)) ∈ within := by
      rw [htop]
      trivial
    exact hwithin
  refine ⟨ambient, ?_⟩
  change smaller = (ambient : Subgroup G)
  rw [← hmap, Subgroup.map_comap_eq, Subgroup.subtype_range,
    inf_eq_left.mpr hambient_le]

theorem stronglyEmbedded_index_odd (subgroup : Subgroup G)
    (hstrong : IsStronglyEmbedded subgroup) : Odd subgroup.index := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let sylow : Sylow 2 subgroup := Classical.choice inferInstance
  obtain ⟨ambient, hmap⟩ := stronglyEmbedded_sylow_inheritance subgroup hstrong sylow
  have hle : (ambient : Subgroup G) ≤ subgroup := by
    rw [← hmap]
    exact Subgroup.map_subtype_le _
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact ambient.not_dvd_index
    ((even_iff_two_dvd.mp heven).trans (Subgroup.index_dvd_of_le hle))

end CFSG.DisconnectedInvolutionGraph.Helpers
