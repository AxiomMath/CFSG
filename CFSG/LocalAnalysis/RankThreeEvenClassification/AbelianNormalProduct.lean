module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalizedProduct

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

theorem abelian_inf_le_centralizer_sup {G : Type u} [Group G]
    (first second : Subgroup G) (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second) :
    first ⊓ second ≤ Subgroup.centralizer ((first ⊔ second : Subgroup G) : Set G) := by
  intro element helement
  have hcentralizer : first ⊔ second ≤ Subgroup.centralizer ({element} : Set G) := by
    apply sup_le
    · intro member hmember
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg (fun value : first => (value : G))
        (isMulCommutative_iff.mp hfirst ⟨member, hmember⟩ ⟨element, helement.1⟩)
    · intro member hmember
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg (fun value : second => (value : G))
        (isMulCommutative_iff.mp hsecond ⟨member, hmember⟩ ⟨element, helement.2⟩)
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcentralizer hmember)

theorem abelian_inf_subgroupOf_sup_le_center {G : Type u} [Group G]
    (first second : Subgroup G) (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second) :
    (first ⊓ second).subgroupOf (first ⊔ second) ≤ Subgroup.center (first ⊔ second : Subgroup G) := by
  intro element helement
  apply Subgroup.mem_center_iff.mpr
  intro member
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (abelian_inf_le_centralizer_sup first second hfirst hsecond helement) member member.property

theorem mutually_normalizing_abelian_sup_commutator_le_inf {G : Type u} [Group G]
    (first second : Subgroup G) (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second)
    (hfirstNormalizes : first ≤ Subgroup.normalizer (second : Set G))
    (hsecondNormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    (commutator (first ⊔ second : Subgroup G)).map (first ⊔ second : Subgroup G).subtype ≤ first ⊓ second := by
  have : (first.subgroupOf (first ⊔ second)).Normal := left_normal_in_sup_of_normalizes first second hsecondNormalizes
  have : (second.subgroupOf (first ⊔ second)).Normal :=
    normal_subgroupOf_of_normalizes second (first ⊔ second) (sup_le hfirstNormalizes Subgroup.le_normalizer)
  have : IsMulCommutative first := hfirst
  have : IsMulCommutative second := hsecond
  have hsup : first.subgroupOf (first ⊔ second) ⊔ second.subgroupOf (first ⊔ second) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hleFirst : commutator (first ⊔ second : Subgroup G) ≤ first.subgroupOf (first ⊔ second) :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
  have hleSecond : commutator (first ⊔ second : Subgroup G) ≤ second.subgroupOf (first ⊔ second) :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      ((sup_comm (second.subgroupOf (first ⊔ second)) (first.subgroupOf (first ⊔ second))).trans hsup) inferInstance
  rintro element ⟨representative, hrepresentative, rfl⟩
  exact ⟨hleFirst hrepresentative, hleSecond hrepresentative⟩

theorem mutually_normalizing_abelian_sup_classTwo {G : Type u} [Group G]
    (first second : Subgroup G) (hfirst : IsMulCommutative first) (hsecond : IsMulCommutative second)
    (hfirstNormalizes : first ≤ Subgroup.normalizer (second : Set G))
    (hsecondNormalizes : second ≤ Subgroup.normalizer (first : Set G)) :
    commutator (first ⊔ second : Subgroup G) ≤ Subgroup.center (first ⊔ second : Subgroup G) := by
  intro element helement
  apply abelian_inf_subgroupOf_sup_le_center first second hfirst hsecond
  exact mutually_normalizing_abelian_sup_commutator_le_inf first second hfirst hsecond
    hfirstNormalizes hsecondNormalizes (Subgroup.mem_map.mpr ⟨element, helement, rfl⟩)

end CFSG.RankThreeEvenClassification.Helpers
