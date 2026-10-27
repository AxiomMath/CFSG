module

public import CFSG.CharacterTheory.TwoRankLowerBound.CyclicTwoSubgroups

public section

open CFSG.Open

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def cyclicRootSet {G : Type*} [Group G] (element : G) : Set G :=
  {root | element ∈ Subgroup.zpowers root}

theorem centralizer_unique_involution_of_twoRank_le_one {G : Type*} [Group G] [Finite G]
    (hrank : CFSG.Open.twoRank G ≤ 1)
    (involution : G) (horder : orderOf involution = 2) :
    ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution := by
  intro other hcentralizer hother
  apply commuting_involutions_eq_of_twoRank_le_one G hrank other involution hother horder
  exact (Subgroup.mem_centralizer_iff.mp hcentralizer involution (by simp)).symm

theorem cyclicRootSet_self {G : Type*} [Group G] (element : G) :
    element ∈ cyclicRootSet element := Subgroup.mem_zpowers element

theorem cyclicRootSet_mono_of_mem_zpowers {G : Type*} [Group G] (left right : G)
    (hmember : left ∈ Subgroup.zpowers right) : cyclicRootSet right ⊆ cyclicRootSet left := by
  intro root hroot
  have hinclusion : Subgroup.zpowers right ≤ Subgroup.zpowers root :=
    Subgroup.zpowers_le.mpr hroot
  exact hinclusion hmember

theorem one_not_mem_cyclicRootSet {G : Type*} [Group G] (element : G) (hne : element ≠ 1) :
    (1 : G) ∉ cyclicRootSet element := by
  intro hroot
  change element ∈ Subgroup.zpowers (1 : G) at hroot
  simp only [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hroot
  exact hne hroot

theorem cyclicRootSet_inv_iff {G : Type*} [Group G] (element root : G) :
    root⁻¹ ∈ cyclicRootSet element ↔ root ∈ cyclicRootSet element := by
  change element ∈ Subgroup.zpowers root⁻¹ ↔ element ∈ Subgroup.zpowers root
  rw [Subgroup.zpowers_inv]

theorem cyclicRootSet_subset_centralizer {G : Type*} [Group G] (element : G) :
    cyclicRootSet element ⊆ Subgroup.centralizer ({element} : Set G) := by
  intro root hroot
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hmember : member = element := Set.mem_singleton_iff.mp hmember
  subst member
  obtain ⟨exponent, rfl⟩ := Subgroup.mem_zpowers_iff.mp hroot
  exact ((Commute.refl root).zpow_left exponent).eq

theorem commuting_involutions_eq_in_cyclic_subgroup {G : Type*} [Group G] [Finite G]
    (cyclic : Subgroup G) [IsCyclic cyclic] (left right : G)
    (hleft : left ∈ cyclic) (hright : right ∈ cyclic)
    (hleftorder : orderOf left = 2) (hrightorder : orderOf right = 2) : left = right := by
  have hrank : twoRank cyclic ≤ 1 := twoRank_le_one_of_abelian_subgroups_cyclic cyclic
    (fun subgroup _ => inferInstance)
  have hleftsuborder : orderOf (⟨left, hleft⟩ : cyclic) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans hleftorder
  have hrightsuborder : orderOf (⟨right, hright⟩ : cyclic) = 2 :=
    (Subgroup.orderOf_coe _).symm.trans hrightorder
  have hcommute := (Subgroup.le_centralizer cyclic) hright
  have hequal := commuting_involutions_eq_of_twoRank_le_one cyclic hrank
    ⟨left, hleft⟩ ⟨right, hright⟩ hleftsuborder hrightsuborder
    (Subtype.ext (Subgroup.mem_centralizer_iff.mp hcommute left hleft))
  exact congrArg Subtype.val hequal

theorem involution_root_conjugate_overlap_centralizes {G : Type*} [Group G] [Finite G]
    (involution root conjugator : G) (horder : orderOf involution = 2)
    (hroot : root ∈ cyclicRootSet involution)
    (hconjugateroot : root ∈ cyclicRootSet (conjugator * involution * conjugator⁻¹)) :
    conjugator ∈ Subgroup.centralizer ({involution} : Set G) := by
  have hconjugateorder : orderOf (conjugator * involution * conjugator⁻¹) = 2 := by
    rw [← MulAut.conj_apply, (MulAut.conj conjugator).orderOf_eq, horder]
  have hequal := commuting_involutions_eq_in_cyclic_subgroup (Subgroup.zpowers root)
    involution (conjugator * involution * conjugator⁻¹) hroot hconjugateroot
    horder hconjugateorder
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hmember : member = involution := Set.mem_singleton_iff.mp hmember
  subst member
  calc
    involution * conjugator = (conjugator * involution * conjugator⁻¹) * conjugator :=
      congrArg (fun element : G => element * conjugator) hequal
    _ = conjugator * involution := by group

theorem cyclicRootSet_conjugate {G : Type*} [Group G] (element root conjugator : G) :
    conjugator * root * conjugator⁻¹ ∈ cyclicRootSet (conjugator * element * conjugator⁻¹) ↔
      root ∈ cyclicRootSet element := by
  constructor
  · intro hroot
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hroot
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨exponent, ?_⟩
    rw [conj_zpow] at hexponent
    exact (MulAut.conj conjugator).injective hexponent
  · intro hroot
    obtain ⟨exponent, hexponent⟩ := Subgroup.mem_zpowers_iff.mp hroot
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨exponent, ?_⟩
    rw [conj_zpow, hexponent]

theorem subgroups_eq_of_same_card_inside_cyclic {G : Type*} [Group G] [Finite G]
    (cyclic left right : Subgroup G) [IsCyclic cyclic] (hleft : left ≤ cyclic)
    (hright : right ≤ cyclic) (hcard : Nat.card left = Nat.card right) : left = right := by
  let : CommGroup cyclic := IsCyclic.commGroup
  have hleftcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hleft).toEquiv
  have hrightcard := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hright).toEquiv
  have hequal : left.subgroupOf cyclic = right.subgroupOf cyclic := by
    rw [subgroup_eq_power_kernel_of_cyclic cyclic (left.subgroupOf cyclic),
      subgroup_eq_power_kernel_of_cyclic cyclic (right.subgroupOf cyclic),
      hleftcard, hrightcard, hcard]
  have hmap := congrArg (Subgroup.map cyclic.subtype) hequal
  simpa only [Subgroup.map_subgroupOf_eq_of_le hleft,
    Subgroup.map_subgroupOf_eq_of_le hright] using hmap

theorem root_conjugate_overlap_normalizes {G : Type*} [Group G] [Finite G]
    (element root conjugator : G) (hroot : root ∈ cyclicRootSet element)
    (hconjugateroot : root ∈ cyclicRootSet (conjugator * element * conjugator⁻¹)) :
    conjugator ∈ Subgroup.normalizer (Subgroup.zpowers element : Set G) := by
  have hequal : Subgroup.zpowers element =
      Subgroup.zpowers (conjugator * element * conjugator⁻¹) := by
    apply subgroups_eq_of_same_card_inside_cyclic (Subgroup.zpowers root)
    · exact Subgroup.zpowers_le_of_mem hroot
    · exact Subgroup.zpowers_le_of_mem hconjugateroot
    · rw [Nat.card_zpowers, Nat.card_zpowers, ← MulAut.conj_apply,
        (MulAut.conj conjugator).orderOf_eq]
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  exact hequal.symm

theorem cyclicRootSet_disjoint_conjugate {G : Type*} [Group G] [Finite G]
    (element conjugator : G)
    (houtside : conjugator ∉ Subgroup.normalizer (Subgroup.zpowers element : Set G)) :
    Disjoint (cyclicRootSet element)
      (cyclicRootSet (conjugator * element * conjugator⁻¹)) := by
  apply Set.disjoint_left.mpr
  intro root hroot hconjugateroot
  exact houtside (root_conjugate_overlap_normalizes element root conjugator hroot hconjugateroot)

theorem involution_not_mem_cyclicRootSet_of_order_gt_two {G : Type*} [Group G]
    (element involution : G) (horder : 2 < orderOf element) (hinvolution : orderOf involution = 2) :
    involution ∉ cyclicRootSet element := by
  intro hroot
  have hdivides := orderOf_dvd_of_mem_zpowers hroot
  rw [hinvolution] at hdivides
  have hle := Nat.le_of_dvd (by omega : 0 < 2) hdivides
  omega

theorem involution_cyclicRootSet_disjoint_conjugate {G : Type*} [Group G] [Finite G]
    (involution conjugator : G) (horder : orderOf involution = 2)
    (houtside : conjugator ∉ Subgroup.centralizer ({involution} : Set G)) :
    Disjoint (cyclicRootSet involution)
      (cyclicRootSet (conjugator * involution * conjugator⁻¹)) := by
  apply Set.disjoint_left.mpr
  intro root hroot hconjugateroot
  exact houtside (involution_root_conjugate_overlap_centralizes involution root conjugator
    horder hroot hconjugateroot)

theorem involution_product_root_factors_centralize {G : Type*} [Group G] [Finite G]
    (involution left right : G) (horder : orderOf involution = 2)
    (hleft : orderOf left = 2) (hright : orderOf right = 2)
    (hroot : left * right ∈ cyclicRootSet involution) :
    left ∈ Subgroup.centralizer ({involution} : Set G) ∧
      right ∈ Subgroup.centralizer ({involution} : Set G) := by
  have hleftinv : left⁻¹ = left := inv_eq_self_of_orderOf_eq_two hleft
  have hrightinv : right⁻¹ = right := inv_eq_self_of_orderOf_eq_two hright
  have hleftconj : left * (left * right) * left⁻¹ = (left * right)⁻¹ := by
    rw [mul_inv_rev, hleftinv, hrightinv]
    have hleftsquare := (orderOf_eq_prime_iff.mp hleft).1
    rw [pow_two] at hleftsquare
    simp only [← mul_assoc, hleftsquare, one_mul]
  have hrightconj : right * (left * right) * right⁻¹ = (left * right)⁻¹ := by
    rw [mul_inv_rev, hleftinv, hrightinv]
    have hrightsquare := (orderOf_eq_prime_iff.mp hright).1
    rw [pow_two] at hrightsquare
    simp only [mul_assoc, hrightsquare, mul_one]
  have hconjugateroot : ∀ conjugator : G,
      conjugator * (left * right) * conjugator⁻¹ = (left * right)⁻¹ →
      left * right ∈ cyclicRootSet (conjugator * involution * conjugator⁻¹) := by
    intro conjugator hconjugate
    have hconjroot := (cyclicRootSet_conjugate involution (left * right) conjugator).mpr hroot
    rw [hconjugate] at hconjroot
    exact (cyclicRootSet_inv_iff _ _).mp hconjroot
  exact ⟨involution_root_conjugate_overlap_centralizes involution (left * right) left horder
      hroot (hconjugateroot left hleftconj),
    involution_root_conjugate_overlap_centralizes involution (left * right) right horder
      hroot (hconjugateroot right hrightconj)⟩

theorem involution_product_not_mem_rootSet_of_unique_centralizer_involution
    {G : Type*} [Group G] [Finite G] (involution left right : G)
    (horder : orderOf involution = 2) (hleft : orderOf left = 2) (hright : orderOf right = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution) :
    left * right ∉ cyclicRootSet involution := by
  intro hroot
  obtain ⟨hleftcentralizes, hrightcentralizes⟩ :=
    involution_product_root_factors_centralize involution left right horder hleft hright hroot
  rw [hunique left hleftcentralizes hleft, hunique right hrightcentralizes hright,
    ← pow_two, (orderOf_eq_prime_iff.mp horder).1] at hroot
  exact one_not_mem_cyclicRootSet involution (orderOf_eq_prime_iff.mp horder).2 hroot

theorem involution_product_not_mem_conjugate_rootSet_of_unique_centralizer_involution
    {G : Type*} [Group G] [Finite G] (involution left right conjugator : G)
    (horder : orderOf involution = 2) (hleft : orderOf left = 2) (hright : orderOf right = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution) :
    conjugator⁻¹ * (left * right) * conjugator ∉ cyclicRootSet involution := by
  have hleftorder : orderOf (conjugator⁻¹ * left * conjugator) = 2 := by
    have hequal := (MulAut.conj conjugator⁻¹).orderOf_eq left
    simpa only [MulAut.conj_apply, inv_inv, hleft] using hequal
  have hrightorder : orderOf (conjugator⁻¹ * right * conjugator) = 2 := by
    have hequal := (MulAut.conj conjugator⁻¹).orderOf_eq right
    simpa only [MulAut.conj_apply, inv_inv, hright] using hequal
  have hnot := involution_product_not_mem_rootSet_of_unique_centralizer_involution involution
    (conjugator⁻¹ * left * conjugator) (conjugator⁻¹ * right * conjugator)
    horder hleftorder hrightorder hunique
  have hproduct : (conjugator⁻¹ * left * conjugator) *
      (conjugator⁻¹ * right * conjugator) = conjugator⁻¹ * (left * right) * conjugator := by group
  rwa [hproduct] at hnot

end CFSG.TwoRankLowerBound.Helpers
