module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicTwoSubgroups

public section

namespace CFSG.TwoRankLowerBound.Helpers

noncomputable def cyclicPowerHom {G : Type*} [Group G] (element : G) (power : ℕ) :
    (Subgroup.zpowers element) →* (Subgroup.zpowers element) := by
  let : CommGroup (Subgroup.zpowers element) := IsCyclic.commGroup
  exact powMonoidHom power

theorem zpowers_power_range {G : Type*} [Group G] (element : G) (power : ℕ) :
    Subgroup.map (Subgroup.zpowers element).subtype
      (cyclicPowerHom element power).range =
      Subgroup.zpowers (element ^ power) := by
  apply le_antisymm
  · rintro member ⟨image, ⟨preimage, rfl⟩, rfl⟩
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp preimage.property
    change (preimage : G) ^ power ∈ Subgroup.zpowers (element ^ power)
    rw [← hexponent]
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨exponent, ?_⟩
    rw [← zpow_natCast (element ^ exponent) power,
      ← zpow_natCast element power, ← zpow_mul, ← zpow_mul, mul_comm]
  · apply Subgroup.zpowers_le.mpr
    exact ⟨⟨element ^ power, (Subgroup.zpowers element).pow_mem
      (Subgroup.mem_zpowers element) power⟩,
      ⟨⟨element, Subgroup.mem_zpowers element⟩, rfl⟩, rfl⟩

theorem cyclic_two_group_square_root_layers {G : Type*} [Group G] [Finite G]
    (htwo : IsPGroup 2 G) (generator root : G)
    (horder : 2 < orderOf generator) (hroot : root ∈ Subgroup.zpowers generator) :
    generator ^ 2 ∈ Subgroup.zpowers root ↔
      root ∉ Subgroup.zpowers (generator ^ 4) := by
  have hsquareNe : generator ^ 2 ≠ 1 := by
    intro hone
    have hdiv := orderOf_dvd_of_pow_eq_one hone
    have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega
  have hnot : generator ^ 2 ∉ Subgroup.zpowers (generator ^ 4) := by
    have hdiv := htwo.dvd_orderOf hsquareNe
    have heq : (generator ^ 2) ^ 2 = generator ^ 4 := by rw [← pow_mul]
    rw [← heq, mem_zpowers_pow_iff, Nat.gcd_eq_left hdiv]
    omega
  constructor
  · intro hcontains hfourth
    exact hnot ((Subgroup.zpowers_le_of_mem hfourth) hcontains)
  · intro hnotfourth
    by_contra hnotcontains
    let cyclic := Subgroup.zpowers generator
    let : CommGroup cyclic := IsCyclic.commGroup
    have hrootLe : Subgroup.zpowers root ≤ cyclic := Subgroup.zpowers_le_of_mem hroot
    have hsquareLe : Subgroup.zpowers (generator ^ 2) ≤ cyclic :=
      Subgroup.zpowers_le_of_mem (Subgroup.npow_mem_zpowers generator 2)
    have hcompare := subgroups_comparable_of_cyclic_two_group cyclic
      (htwo.to_subgroup cyclic) ((Subgroup.zpowers root).subgroupOf cyclic)
      ((Subgroup.zpowers (generator ^ 2)).subgroupOf cyclic)
    have hle : Subgroup.zpowers root ≤ Subgroup.zpowers (generator ^ 2) := by
      rcases hcompare with hle | hle
      · have hmap := Subgroup.map_mono hle (f := cyclic.subtype)
        simpa only [Subgroup.map_subgroupOf_eq_of_le hrootLe,
          Subgroup.map_subgroupOf_eq_of_le hsquareLe] using hmap
      · have hmap := Subgroup.map_mono hle (f := cyclic.subtype)
        have hreverse : Subgroup.zpowers (generator ^ 2) ≤ Subgroup.zpowers root := by
          simpa only [Subgroup.map_subgroupOf_eq_of_le hrootLe,
            Subgroup.map_subgroupOf_eq_of_le hsquareLe] using hmap
        exact False.elim (hnotcontains (hreverse (Subgroup.mem_zpowers _)))
    let squares := Subgroup.zpowers (generator ^ 2)
    let : CommGroup squares := IsCyclic.commGroup
    have hproper : (Subgroup.zpowers root).subgroupOf squares ≠ ⊤ := by
      intro hequal
      exact hnotcontains ((Subgroup.subgroupOf_eq_top.mp hequal) (Subgroup.mem_zpowers _))
    have hsmall := proper_subgroup_le_squares_of_cyclic_two_group squares
      (htwo.to_subgroup squares) ((Subgroup.zpowers root).subgroupOf squares) hproper
    have hmap := Subgroup.map_mono hsmall (f := squares.subtype)
    rw [Subgroup.map_subgroupOf_eq_of_le hle] at hmap
    change Subgroup.zpowers root ≤ Subgroup.map squares.subtype
      (cyclicPowerHom (generator ^ 2) 2).range at hmap
    rw [zpowers_power_range] at hmap
    have hpower : (generator ^ 2) ^ 2 = generator ^ 4 := by rw [← pow_mul]
    rw [hpower] at hmap
    exact hnotfourth (hmap (Subgroup.mem_zpowers root))

end CFSG.TwoRankLowerBound.Helpers
