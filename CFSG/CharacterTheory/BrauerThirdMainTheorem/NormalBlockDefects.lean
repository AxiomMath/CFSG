module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalPVanishing
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.ClassDefects

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem class_meets_centralizer_iff {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {subgroup defect : Subgroup G}
    (hpGroup : IsPGroup prime subgroup) {conjugacyClass : ConjClasses G}
    (hdefect : classDefect prime conjugacyClass defect) :
    (∃ element : G, ConjClasses.mk element = conjugacyClass ∧
      element ∈ Subgroup.centralizer (subgroup : Set G)) ↔
        subgroupSubconjugate subgroup defect := by
  constructor
  · rintro ⟨element, helement, hcentralizes⟩
    apply pGroup_centralizes_subconjugate_classDefect prime hprime helement hpGroup
      _ hdefect
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    exact (Subgroup.mem_centralizer_iff.mp hcentralizes member hmember).symm
  · rintro ⟨conjugator, hinclusion⟩
    obtain ⟨representative, hrepresentative, hdefectCentralizes⟩ :=
      classDefect_centralizes prime hdefect
    refine ⟨conjugator⁻¹ * representative * conjugator, ?_, ?_⟩
    · have hconjugate : ConjClasses.mk (conjugator⁻¹ * representative * conjugator) =
          ConjClasses.mk representative := by
        apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        exact (isConj_iff.mpr ⟨conjugator⁻¹, by simp only [inv_inv]⟩).symm
      exact hconjugate.trans hrepresentative
    · apply Subgroup.mem_centralizer_iff.mpr
      intro member hmember
      have hmemberDefect := hinclusion (Subgroup.mem_map.mpr ⟨member, hmember, rfl⟩)
      have hcommute := Subgroup.mem_centralizer_iff.mp (hdefectCentralizes hmemberDefect)
        representative (Set.mem_singleton representative)
      change representative * (conjugator * member * conjugator⁻¹) =
        (conjugator * member * conjugator⁻¹) * representative at hcommute
      have hequal := congrArg (fun value => conjugator⁻¹ * value * conjugator) hcommute
      have hleft : conjugator⁻¹ * (representative *
          (conjugator * member * conjugator⁻¹)) * conjugator =
          (conjugator⁻¹ * representative * conjugator) * member := by group
      have hright : conjugator⁻¹ * ((conjugator * member * conjugator⁻¹) *
          representative) * conjugator =
          member * (conjugator⁻¹ * representative * conjugator) := by group
      rw [hleft, hright] at hequal
      exact hequal.symm

theorem class_centralizer_mem_of_normal {G : Type*} [Group G]
    (subgroup : Subgroup G) [subgroup.Normal] {first second : G}
    (hclass : ConjClasses.mk first = ConjClasses.mk second)
    (hfirst : first ∈ Subgroup.centralizer (subgroup : Set G)) :
    second ∈ Subgroup.centralizer (subgroup : Set G) := by
  obtain ⟨conjugator, rfl⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hclass)
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  have hconjugateMem : conjugator⁻¹ * member * conjugator ∈ subgroup := by
    simpa only [inv_inv] using (inferInstance : subgroup.Normal).conj_mem member hmember conjugator⁻¹
  have hcommute := Subgroup.mem_centralizer_iff.mp hfirst _ hconjugateMem
  calc
    member * (conjugator * first * conjugator⁻¹) =
        conjugator * ((conjugator⁻¹ * member * conjugator) * first) * conjugator⁻¹ := by group
    _ = conjugator * (first * (conjugator⁻¹ * member * conjugator)) * conjugator⁻¹ := by rw [hcommute]
    _ = _ := by group

theorem normalPSubgroup_le_classDefect {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (subgroup : Subgroup G) [subgroup.Normal]
    (hpGroup : IsPGroup prime subgroup) {conjugacyClass : ConjClasses G}
    (hmeets : ∃ element : G, ConjClasses.mk element = conjugacyClass ∧
      element ∈ Subgroup.centralizer (subgroup : Set G))
    {defect : Subgroup G} (hdefect : classDefect prime conjugacyClass defect) :
    subgroup ≤ defect := by
  obtain ⟨element, helement, helementCentralizes⟩ := hmeets
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hdefect
  have hrepresentativeCentralizes := class_centralizer_mem_of_normal subgroup
    (helement.trans hrepresentative.symm) helementCentralizes
  have hinclusion : subgroup ≤ Subgroup.centralizer {representative} := by
    intro member hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    exact (Subgroup.mem_centralizer_iff.mp hrepresentativeCentralizes member hmember).symm
  have hpLocal : IsPGroup prime (subgroup.subgroupOf (Subgroup.centralizer {representative})) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  have hle := hpLocal.le_sylow_of_normal sylow
  rw [← Subgroup.map_subgroupOf_eq_of_le hinclusion]
  exact Subgroup.map_mono hle

theorem normalPSubgroup_le_blockDefect (prime : ℕ) (hprime : prime.Prime)
    (m : Ideal BlocksAlgInt) (hm : m.IsMaximal) (hprimeMem : (prime : BlocksAlgInt) ∈ m)
    (G : Type) [Group G] [Finite G] (subgroup : Subgroup G) [subgroup.Normal]
    (hpGroup : IsPGroup prime subgroup) {character : G → ℂ}
    (hcharacter : character ∈ BlocksIrr G) {defect : Subgroup G}
    (hdefect : blockDefect prime m character defect) : subgroup ≤ defect := by
  obtain ⟨conjugacyClass, hclassDefect, hnonzero⟩ := hdefect.1
  apply normalPSubgroup_le_classDefect prime subgroup hpGroup _ hclassDefect
  by_contra hnotExists
  push Not at hnotExists
  exact hnonzero (normalPSubgroup_centralChar_vanishes prime hprime m hm hprimeMem G subgroup
    hpGroup hcharacter (classCoefficients_central m hm conjugacyClass) (by
      intro element hcentralizes
      have hnotClass : ConjClasses.mk element ≠ conjugacyClass :=
        fun hclass => hnotExists element hclass hcentralizes
      simp only [classCoefficients, ite_eq_right hnotClass]))

end CFSG.BrauerThirdMainTheorem.Helpers
