module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CubicActions
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ReplacementProduct

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem subgroup_classTwo_of_commutator_centralized {G : Type u} [Group G]
    (subgroup : Subgroup G) (hclass : ⁅subgroup, subgroup⁆ ≤ Subgroup.centralizer (subgroup : Set G)) :
    commutator subgroup ≤ Subgroup.center subgroup := by
  have hmapped : (commutator subgroup).map subgroup.subtype = ⁅subgroup, subgroup⁆ := by
    rw [map_commutator_eq, Subgroup.range_subtype]
  intro element helement
  have hambient : (element : G) ∈ ⁅subgroup, subgroup⁆ := by
    rw [← hmapped]
    exact Subgroup.mem_map.mpr ⟨element, helement, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro member
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hclass hambient) member member.property

theorem ReplacementDatum.join_derived_le_intersection {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    (commutator (replacementJoin abelian element)).map (replacementJoin abelian element).subtype ≤
      replacementIntersection abelian element :=
  mutually_normalizing_abelian_sup_commutator_le_inf abelian (replacementConjugate abelian element) datum.maximum.1
    (replacementConjugate_commutative abelian element datum.maximum.1)
    datum.mutually_normalizing.1 datum.mutually_normalizing.2

theorem ReplacementDatum.sourceDifference_mem_join {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (_datum : ReplacementDatum prime normal abelian element)
    (member : G) (hmember : member ∈ abelian) :
    element⁻¹ * member * element * member⁻¹ ∈ replacementJoin abelian element := by
  have hconjugate : element⁻¹ * member * element ∈ replacementConjugate abelian element := by
    refine Subgroup.mem_map.mpr ⟨member, hmember, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact (replacementJoin abelian element).mul_mem
    ((le_sup_right : replacementConjugate abelian element ≤ replacementJoin abelian element) hconjugate)
    ((le_sup_left : abelian ≤ replacementJoin abelian element) (abelian.inv_mem hmember))

theorem ReplacementDatum.cubic_sourceDifference {G : Type u} [Group G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element)
    (first second third : G) (hfirst : first ∈ abelian) (hsecond : second ∈ abelian)
    (hthird : third ∈ abelian) :
    let difference := element⁻¹ * first * element * first⁻¹
    let mixed := difference⁻¹ * second * difference * second⁻¹
    mixed⁻¹ * third * mixed * third⁻¹ = 1 := by
  dsimp only
  let difference := element⁻¹ * first * element * first⁻¹
  have hdifference : difference ∈ replacementJoin abelian element := datum.sourceDifference_mem_join first hfirst
  have hsecondJoin : second ∈ replacementJoin abelian element :=
    (le_sup_left : abelian ≤ replacementJoin abelian element) hsecond
  have hcommutator : difference⁻¹ * second * difference * second⁻¹ ∈ replacementIntersection abelian element := by
    apply datum.join_derived_le_intersection
    refine Subgroup.mem_map.mpr ⟨⁅(⟨difference, hdifference⟩ : replacementJoin abelian element)⁻¹,
      (⟨second, hsecondJoin⟩ : replacementJoin abelian element)⁆, ?_, ?_⟩
    · exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · change difference⁻¹ * second * (difference⁻¹)⁻¹ * second⁻¹ = _
      rw [inv_inv]
  have hcommute : third * (difference⁻¹ * second * difference * second⁻¹) =
      (difference⁻¹ * second * difference * second⁻¹) * third :=
    congrArg (fun value : abelian => (value : G))
      (isMulCommutative_iff.mp datum.maximum.1 ⟨third, hthird⟩ ⟨_, hcommutator.1⟩)
  change (difference⁻¹ * second * difference * second⁻¹)⁻¹ * third *
    (difference⁻¹ * second * difference * second⁻¹) * third⁻¹ = 1
  rw [mul_assoc _ third, hcommute]
  group

theorem normal_conjugation_difference_apply {G : Type u} [Group G]
    (normal : Subgroup G) [normal.Normal] (member : G) (element : normal) :
    normal.subtype (automorphismDifference (MulAut.conjNormal member : MulAut normal) element) =
      (element : G)⁻¹ * member * element * member⁻¹ := by
  change (element : G)⁻¹ * ((MulAut.conjNormal member) element : G) = _
  rw [MulAut.conjNormal_apply]
  group

theorem ReplacementDatum.commutators_abelian {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    IsMulCommutative (replacementCommutators abelian element) := by
  have : normal.Normal := datum.normal_normal
  let action : abelian →* MulAut normal := (MulAut.conjNormal : G →* MulAut normal).comp abelian.subtype
  let internal : normal := ⟨element, datum.element_mem⟩
  have hclass : commutator normal ≤ Subgroup.center normal :=
    subgroup_classTwo_of_commutator_centralized normal datum.class_two
  have hderivedMap : (commutator normal).map normal.subtype = ⁅normal, normal⁆ := by
    rw [map_commutator_eq, Subgroup.range_subtype]
  have hfixed : ∀ member : abelian, ∀ value ∈ commutator normal, action member value = value := by
    intro member value hvalue
    have hambient : (value : G) ∈ ⁅normal, normal⁆ := by
      rw [← hderivedMap]
      exact Subgroup.mem_map.mpr ⟨value, hvalue, rfl⟩
    have hab : (value : G) ∈ abelian := datum.derived_le_abelian hambient
    apply Subtype.ext
    change ((MulAut.conjNormal (member : G)) value : G) = value
    rw [MulAut.conjNormal_apply]
    have heq := congrArg (fun value : abelian => (value : G))
      (isMulCommutative_iff.mp datum.maximum.1 member ⟨value, hab⟩)
    change (member : G) * (value : G) = (value : G) * member at heq
    rw [heq]
    group
  have hcubic : ∀ first second third : abelian,
      automorphismDifference (action third)
        (automorphismDifference (action second) (automorphismDifference (action first) internal)) = 1 := by
    intro first second third
    apply Subtype.ext
    change normal.subtype (automorphismDifference (MulAut.conjNormal (third : G))
      (automorphismDifference (MulAut.conjNormal (second : G))
        (automorphismDifference (MulAut.conjNormal (first : G)) internal))) = 1
    rw [normal_conjugation_difference_apply]
    change (normal.subtype (automorphismDifference (MulAut.conjNormal (second : G))
      (automorphismDifference (MulAut.conjNormal (first : G)) internal)))⁻¹ * (third : G) *
      normal.subtype (automorphismDifference (MulAut.conjNormal (second : G))
        (automorphismDifference (MulAut.conjNormal (first : G)) internal)) * (third : G)⁻¹ = 1
    rw [normal_conjugation_difference_apply]
    change ((normal.subtype (automorphismDifference (MulAut.conjNormal (first : G)) internal))⁻¹ *
        (second : G) * normal.subtype (automorphismDifference (MulAut.conjNormal (first : G)) internal) *
          (second : G)⁻¹)⁻¹ * (third : G) *
        ((normal.subtype (automorphismDifference (MulAut.conjNormal (first : G)) internal))⁻¹ *
          (second : G) * normal.subtype (automorphismDifference (MulAut.conjNormal (first : G)) internal) *
            (second : G)⁻¹) * (third : G)⁻¹ = 1
    rw [normal_conjugation_difference_apply]
    exact datum.cubic_sourceDifference first second third first.property second.property third.property
  have hgenerated := cubic_classTwo_generated_differences_abelian prime datum.prime_odd
    (datum.p_group.to_subgroup normal) hclass datum.maximum.1 action hfixed internal hcubic
  apply CFSG.subgroup_isMulCommutative_closure
  rintro firstValue ⟨first, hfirst, rfl⟩ secondValue ⟨second, hsecond, rfl⟩
  let firstMember : abelian := ⟨first, hfirst⟩
  let secondMember : abelian := ⟨second, hsecond⟩
  let generated := Subgroup.closure (Set.range (fun member => automorphismDifference (action member) internal))
  have hfirstMem : automorphismDifference (action firstMember⁻¹) internal ∈ generated :=
    Subgroup.subset_closure ⟨firstMember⁻¹, rfl⟩
  have hsecondMem : automorphismDifference (action secondMember⁻¹) internal ∈ generated :=
    Subgroup.subset_closure ⟨secondMember⁻¹, rfl⟩
  have hcommute : Commute (automorphismDifference (action firstMember⁻¹) internal)
      (automorphismDifference (action secondMember⁻¹) internal) :=
    congrArg (fun value : generated => (value : normal))
      (isMulCommutative_iff.mp hgenerated ⟨_, hfirstMem⟩ ⟨_, hsecondMem⟩)
  have hmapped := hcommute.inv_inv.map normal.subtype
  have hfirstEq : normal.subtype (automorphismDifference (action firstMember⁻¹) internal)⁻¹ =
      first⁻¹ * element⁻¹ * first * element := by
    rw [map_inv]
    change (normal.subtype (automorphismDifference (MulAut.conjNormal first⁻¹) internal))⁻¹ = _
    rw [normal_conjugation_difference_apply]
    change (element⁻¹ * first⁻¹ * element * (first⁻¹)⁻¹)⁻¹ = _
    group
  have hsecondEq : normal.subtype (automorphismDifference (action secondMember⁻¹) internal)⁻¹ =
      second⁻¹ * element⁻¹ * second * element := by
    rw [map_inv]
    change (normal.subtype (automorphismDifference (MulAut.conjNormal second⁻¹) internal))⁻¹ = _
    rw [normal_conjugation_difference_apply]
    change (element⁻¹ * second⁻¹ * element * (second⁻¹)⁻¹)⁻¹ = _
    group
  rw [hfirstEq, hsecondEq] at hmapped
  exact hmapped.eq

theorem ReplacementDatum.subgroup_abelian {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    IsMulCommutative (replacementSubgroup abelian element) := by
  have hcentralizes : replacementIntersection abelian element ≤
      Subgroup.centralizer (replacementCommutators abelian element : Set G) :=
    datum.intersection_central.trans
      (Subgroup.centralizer_le (replacementCommutators_le_join abelian element))
  have : IsMulCommutative abelian := datum.maximum.1
  have hintersection : IsMulCommutative (replacementIntersection abelian element) :=
    IsMulCommutative.of_setLike_mul_comm (fun first hfirst second hsecond =>
      congrArg (fun value : abelian => (value : G))
        (isMulCommutative_iff.mp datum.maximum.1 ⟨first, hfirst.1⟩ ⟨second, hsecond.1⟩))
  exact commutative_sup_of_centralizes (replacementIntersection abelian element)
    (replacementCommutators abelian element) hintersection datum.commutators_abelian hcentralizes

theorem ReplacementDatum.subgroup_maximum {G : Type u} [Group G] [Finite G]
    {prime : ℕ} {normal abelian : Subgroup G} {element : G}
    (datum : ReplacementDatum prime normal abelian element) :
    MaximumOrderAbelian (replacementSubgroup abelian element) :=
  ⟨datum.subgroup_abelian, datum.subgroup_card_eq.trans datum.maximum.2⟩

end CFSG.RankThreeEvenClassification.Helpers
