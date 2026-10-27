module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.DefectDefinitions

public section

open CFSG
open scoped Pointwise

namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem sylow_subconjugate_image_internal {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (ambient : Subgroup G)
    (sylow : Sylow prime ambient) {subgroup : Subgroup G}
    (hpGroup : IsPGroup prime subgroup) (hinclusion : subgroup ≤ ambient) :
    ∃ conjugator : ambient, subgroup.map (MulAut.conj conjugator.val).toMonoidHom ≤
      ((sylow : Subgroup ambient).map ambient.subtype) := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hpGroupLocal : IsPGroup prime (subgroup.subgroupOf ambient) :=
    hpGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hinclusion).symm
  obtain ⟨extension, hextension⟩ := hpGroupLocal.exists_le_sylow
  obtain ⟨conjugator, hconjugator⟩ :=
    MulAction.exists_smul_eq ambient extension sylow
  have hconjugated : (extension : Subgroup ambient).map
      (MulAut.conj conjugator).toMonoidHom = (sylow : Subgroup ambient) := by
    have hequal := congrArg Sylow.toSubgroup hconjugator
    exact hequal
  refine ⟨conjugator, ?_⟩
  intro element hmember
  obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
  apply Subgroup.mem_map.mpr
  refine ⟨conjugator * ⟨factor, hinclusion hfactor⟩ * conjugator⁻¹, ?_, rfl⟩
  rw [← hconjugated]
  apply Subgroup.mem_map.mpr
  exact ⟨⟨factor, hinclusion hfactor⟩, hextension hfactor, rfl⟩

theorem sylow_subconjugate_image {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (ambient : Subgroup G)
    (sylow : Sylow prime ambient) {subgroup : Subgroup G}
    (hpGroup : IsPGroup prime subgroup) (hinclusion : subgroup ≤ ambient) :
    subgroupSubconjugate subgroup
      ((sylow : Subgroup ambient).map ambient.subtype) := by
  obtain ⟨conjugator, hinclusion⟩ :=
    sylow_subconjugate_image_internal prime hprime ambient sylow hpGroup hinclusion
  exact ⟨conjugator.val, hinclusion⟩

theorem pGroup_centralizes_subconjugate_classDefect {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {conjugacyClass : ConjClasses G}
    {element : G} (helement : ConjClasses.mk element = conjugacyClass)
    {subgroup defect : Subgroup G} (hpGroup : IsPGroup prime subgroup)
    (hcentralizes : subgroup ≤ Subgroup.centralizer {element})
    (hdefect : classDefect prime conjugacyClass defect) :
    subgroupSubconjugate subgroup defect := by
  obtain ⟨representative, hrepresentative, sylow, rfl⟩ := hdefect
  obtain ⟨conjugator, hconjugator⟩ :=
    isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp
      (helement.trans hrepresentative.symm))
  let conjugated := subgroup.map (MulAut.conj conjugator).toMonoidHom
  have hpConjugated : IsPGroup prime conjugated :=
    hpGroup.of_equiv ((MulAut.conj conjugator).subgroupMap subgroup)
  have hinclusion : conjugated ≤ Subgroup.centralizer {representative} := by
    intro member hmember
    obtain ⟨factor, hfactor, rfl⟩ := Subgroup.mem_map.mp hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro test htest
    obtain rfl := Set.mem_singleton_iff.mp htest
    rw [← hconjugator]
    change (conjugator * element * conjugator⁻¹) *
      (conjugator * factor * conjugator⁻¹) =
      (conjugator * factor * conjugator⁻¹) * (conjugator * element * conjugator⁻¹)
    have hcommute := Subgroup.mem_centralizer_iff.mp (hcentralizes hfactor)
      element (Set.mem_singleton element)
    calc
      _ = conjugator * (element * factor) * conjugator⁻¹ := by group
      _ = conjugator * (factor * element) * conjugator⁻¹ := by rw [hcommute]
      _ = _ := by group
  exact subgroupSubconjugate_trans ⟨conjugator, le_rfl⟩
    (sylow_subconjugate_image prime hprime _ sylow hpConjugated hinclusion)

theorem classDefect_subconjugate {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {conjugacyClass : ConjClasses G}
    {left right : Subgroup G} (hleft : classDefect prime conjugacyClass left)
    (hright : classDefect prime conjugacyClass right) :
    subgroupSubconjugate left right := by
  obtain ⟨element, helement, hcentralizes⟩ := classDefect_centralizes prime hleft
  exact pGroup_centralizes_subconjugate_classDefect prime hprime helement
    (classDefect_isPGroup prime hleft) hcentralizes hright

theorem classDefect_card_eq {G : Type*} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {conjugacyClass : ConjClasses G}
    {left right : Subgroup G} (hleft : classDefect prime conjugacyClass left)
    (hright : classDefect prime conjugacyClass right) : Nat.card left = Nat.card right := by
  exact Nat.le_antisymm
    (subgroupSubconjugate_card_le (classDefect_subconjugate prime hprime hleft hright))
    (subgroupSubconjugate_card_le (classDefect_subconjugate prime hprime hright hleft))

end CFSG.BrauerThirdMainTheorem.Helpers
