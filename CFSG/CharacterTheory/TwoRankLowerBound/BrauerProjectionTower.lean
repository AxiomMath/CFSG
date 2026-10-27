module

public import CFSG.CharacterTheory.TwoRankLowerBound.CentralCoefficientTransport

public section

open scoped Classical Pointwise

namespace CFSG.TwoRankLowerBound.Helpers

theorem relativeCentralizer_mem_iff {group : Type*} [Group group]
    (primary intermediate : Subgroup group) (hcontains : primary ≤ intermediate) (element : intermediate) :
    element ∈ Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate) ↔
      element.val ∈ Subgroup.centralizer (primary : Set group) := by
  constructor
  · intro hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmemberPrimary
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hmember
      (⟨member, hcontains hmemberPrimary⟩ : intermediate) hmemberPrimary)
  · intro hmember
    apply Subgroup.mem_centralizer_iff.mpr
    intro member hmemberPrimary
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hmember member.val hmemberPrimary

theorem centralCoefficientTransport_subgroupOf_coeff {group : Type*} [Group group]
    (ring : Subring ℂ) {subgroup intermediate : Subgroup group} (hcontains : subgroup ≤ intermediate)
    (value : centralCoefficientSubring (G := subgroup.subgroupOf intermediate) ring)
    (element : subgroup.subgroupOf intermediate) :
    (centralCoefficientTransport ring (Subgroup.subgroupOfEquivOfLe hcontains) value).val.coeff
      ((Subgroup.subgroupOfEquivOfLe hcontains) element) = value.val.coeff element := by
  rw [centralCoefficientTransport_coeff, MulEquiv.symm_apply_apply]

theorem relative_brauer_projection_transport {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary intermediate smaller : Subgroup group)
    (hprimary : primary ≤ intermediate) (hsmaller : smaller ≤ intermediate)
    (_hcontains : Subgroup.centralizer (primary : Set group) ≤ smaller)
    (_hnormalizes : smaller ≤ Subgroup.normalizer (primary : Set group))
    (hlocalContains : Subgroup.centralizer (primary.subgroupOf intermediate : Set intermediate) ≤
      smaller.subgroupOf intermediate)
    (hlocalNormalizes : smaller.subgroupOf intermediate ≤
      Subgroup.normalizer (primary.subgroupOf intermediate : Set intermediate))
    (value : centralCoefficientSubring (G := intermediate) ring) :
    ∀ element : smaller.subgroupOf intermediate,
      (centralCoefficientTransport ring (Subgroup.subgroupOfEquivOfLe hsmaller)
        (centralNormalizerCoefficientProjection ring (primary.subgroupOf intermediate)
          (smaller.subgroupOf intermediate) hlocalContains hlocalNormalizes value)).val.coeff
            ((Subgroup.subgroupOfEquivOfLe hsmaller) element) =
        if element.val.val ∈ Subgroup.centralizer (primary : Set group) then
          value.val.coeff element.val else 0 := by
  intro element
  rw [centralCoefficientTransport_subgroupOf_coeff, centralNormalizerCoefficientProjection_coeff,
    relativeCentralizer_mem_iff primary intermediate hprimary]

theorem centralNormalizerCoefficientProjection_tower {group : Type*} [Group group] [Fintype group]
    (ring : Subring ℂ) (primary larger intermediate smaller : Subgroup group)
    (hprimaryLarger : primary ≤ larger) (hlarger : larger ≤ intermediate) (hsmaller : smaller ≤ intermediate)
    (hfirstContains : Subgroup.centralizer (primary : Set group) ≤ intermediate)
    (hfirstNormalizes : intermediate ≤ Subgroup.normalizer (primary : Set group))
    (hcontains : Subgroup.centralizer (larger : Set group) ≤ smaller)
    (hnormalizes : smaller ≤ Subgroup.normalizer (larger : Set group))
    (hlocalContains : Subgroup.centralizer (larger.subgroupOf intermediate : Set intermediate) ≤
      smaller.subgroupOf intermediate)
    (hlocalNormalizes : smaller.subgroupOf intermediate ≤
      Subgroup.normalizer (larger.subgroupOf intermediate : Set intermediate))
    (value : centralCoefficientSubring (G := group) ring) :
    centralCoefficientTransport ring (Subgroup.subgroupOfEquivOfLe hsmaller)
      (centralNormalizerCoefficientProjection ring (larger.subgroupOf intermediate)
        (smaller.subgroupOf intermediate) hlocalContains hlocalNormalizes
        (centralNormalizerCoefficientProjection ring primary intermediate hfirstContains hfirstNormalizes value)) =
      centralNormalizerCoefficientProjection ring larger smaller hcontains hnormalizes value := by
  apply Subtype.ext
  ext element
  let localElement : smaller.subgroupOf intermediate := (Subgroup.subgroupOfEquivOfLe hsmaller).symm element
  have helement : (Subgroup.subgroupOfEquivOfLe hsmaller) localElement = element :=
    MulEquiv.apply_symm_apply _ _
  have hcoefficient := relative_brauer_projection_transport ring larger intermediate smaller hlarger hsmaller
    hcontains hnormalizes hlocalContains hlocalNormalizes
      (centralNormalizerCoefficientProjection ring primary intermediate hfirstContains hfirstNormalizes value) localElement
  rw [helement] at hcoefficient
  rw [hcoefficient, centralNormalizerCoefficientProjection_coeff, centralNormalizerCoefficientProjection_coeff]
  change (if element.val ∈ Subgroup.centralizer (larger : Set group) then
    if element.val ∈ Subgroup.centralizer (primary : Set group) then value.val.coeff element.val else 0 else 0) =
    (if element.val ∈ Subgroup.centralizer (larger : Set group) then value.val.coeff element.val else 0)
  by_cases hmember : element.val ∈ Subgroup.centralizer (larger : Set group)
  · have hprimaryMember : element.val ∈ Subgroup.centralizer (primary : Set group) :=
      Subgroup.centralizer_le hprimaryLarger hmember
    simp only [ite_eq_left hmember, ite_eq_left hprimaryMember]
  · simp only [ite_eq_right hmember]

end CFSG.TwoRankLowerBound.Helpers
