module

public import CFSG.LocalAnalysis.ComponentClassification.BadComponents
public import CFSG.LocalAnalysis.ComponentClassification.BadComponentDetection
public import CFSG.LocalAnalysis.ComponentClassification.SolvableKernelContainment

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BadSolvableQuotients

theorem component_le_kernel {G H : Type*} [Group G] [Group H]
    [Group.IsSolvable H] (homomorphism : G →* H) (component : Subgroup G)
    (hcomponent : TwoComponents.IsTwoComponent component) : component ≤ homomorphism.ker := by
  let : Group.IsPerfect component := ⟨TwoComponents.perfect hcomponent⟩
  have htrivial := SolvableKernelContainment.hom_eq_one (homomorphism.domRestrict component)
  intro element hmem
  have hone := congrArg (fun restriction : component →* H => restriction (⟨element, hmem⟩ : component))
    htrivial
  exact hone

theorem bad_eq_kernel_image {G H : Type*} [Group G] [Finite G] [Group H]
    [Group.IsSolvable H] (homomorphism : G →* H) :
    TwoComponents.badSubgroup G =
      (TwoComponents.badSubgroup homomorphism.ker).map homomorphism.ker.subtype := by
  apply le_antisymm
  · apply sSup_le
    intro component hbad
    have hcontained := component_le_kernel homomorphism component hbad.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hcontained]
    apply Subgroup.map_mono
    apply le_sSup
    refine ⟨TwoComponentTransport.of_overgroup hbad.1 hcontained, ?_⟩
    intro hquasisimple
    exact hbad.2 (Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hcontained).symm hquasisimple)
  · exact BadComponentDetection.subnormal_monotone homomorphism.ker
      (Components.chain_of_mathlib_subnormal
        (Subgroup.IsSubnormal.step homomorphism.ker ⊤ le_top Subgroup.IsSubnormal.top inferInstance))

theorem bad_sup_normal_two {G : Type*} [Group G] [Finite G]
    (normalSubgroup twoSubgroup : Subgroup G) [normalSubgroup.Normal]
    (htwo : IsPGroup 2 twoSubgroup) :
    (TwoComponents.badSubgroup (normalSubgroup ⊔ twoSubgroup : Subgroup G)).map
        (normalSubgroup ⊔ twoSubgroup).subtype ≤
      (TwoComponents.badSubgroup normalSubgroup).map normalSubgroup.subtype := by
  let overgroup := normalSubgroup ⊔ twoSubgroup
  let projection := QuotientGroup.mk' normalSubgroup
  let quotientImage := overgroup.map projection
  have hnormalImage : normalSubgroup.map projection = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
  have himage : quotientImage = twoSubgroup.map projection := by
    change (normalSubgroup ⊔ twoSubgroup).map projection = twoSubgroup.map projection
    rw [Subgroup.map_sup, hnormalImage, bot_sup_eq]
  have hquotientTwo : IsPGroup 2 quotientImage := by rw [himage]; exact htwo.map projection
  let : Group.IsNilpotent quotientImage := hquotientTwo.isNilpotent
  let restriction : overgroup →* quotientImage :=
    (projection.domRestrict overgroup).codRestrict quotientImage
      fun element => Subgroup.mem_map_of_mem projection element.property
  have hkernel : restriction.ker = normalSubgroup.subgroupOf overgroup := by
    ext element
    change restriction element = 1 ↔ element.val ∈ normalSubgroup
    exact ⟨fun hone => (QuotientGroup.eq_one_iff element.val).mp (congrArg Subtype.val hone),
      fun hmem => Subtype.ext ((QuotientGroup.eq_one_iff element.val).mpr hmem)⟩
  have hbad := bad_eq_kernel_image restriction
  rw [hkernel] at hbad
  rw [hbad, Subgroup.map_map]
  let equivalence := Subgroup.subgroupOfEquivOfLe (le_sup_left : normalSubgroup ≤ overgroup)
  have hcomposite : overgroup.subtype.comp (normalSubgroup.subgroupOf overgroup).subtype =
      normalSubgroup.subtype.comp equivalence.toMonoidHom := rfl
  rw [hcomposite, ← Subgroup.map_map, BadComponents.equiv_invariant equivalence]

end CFSG.ComponentClassification.BadSolvableQuotients
