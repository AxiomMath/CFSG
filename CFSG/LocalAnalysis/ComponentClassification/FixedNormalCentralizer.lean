module

public import Mathlib
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Open.Defs
public import CFSG.LocalAnalysis.ComponentClassification.Components
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelTwoComponents
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentTransport
public import CFSG.LocalAnalysis.ComponentClassification.CentralTwoKernelComponents
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.OddKernelNormalizers
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionDiagonal
public import CFSG.LocalAnalysis.ComponentClassification.PerfectCentralQuotient

public section

open CFSG.Open

namespace CFSG.ComponentClassification.FixedNormalCentralizer

@[expose] def equivalence {G : Type*} [Group G] (normalSubgroup : Subgroup G)
    [normalSubgroup.Normal] (element : G) :
    normalSubgroup.subgroupOf (Subgroup.centralizer ({element} : Set G)) ≃*
      FixedCommutingProduct.fixedSubgroup (MulAut.conjNormal (H := normalSubgroup) element) :=
  { toFun := fun member => ⟨⟨member.val.val, member.property⟩, by
      apply Subtype.ext
      change element * member.val.val * element⁻¹ = member.val.val
      have hcommute := Subgroup.mem_centralizer_singleton_iff.mp member.val.property
      rw [← hcommute, mul_inv_cancel_right]⟩
    invFun := fun member => ⟨⟨member.val.val, by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hfixed := congrArg Subtype.val member.property
      change element * member.val.val * element⁻¹ = member.val.val at hfixed
      calc
        member.val.val * element = (element * member.val.val * element⁻¹) * element := by rw [hfixed]
        _ = element * member.val.val := by group⟩, member.val.property⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    map_mul' := fun _ _ => Subtype.ext (Subtype.ext rfl) }

theorem local_component_transport {G : Type*} [Group G] [Finite G]
    (normalSubgroup : Subgroup G) [normalSubgroup.Normal] (element : G)
    (localComponent : Subgroup (Subgroup.centralizer ({element} : Set G)))
    (hlocal : TwoComponents.IsTwoComponent localComponent)
    (hnotQuasisimple : ¬ IsQuasisimple localComponent)
    (hcontained : localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype ≤ normalSubgroup) :
    ∃ fixedComponent : Subgroup (FixedCommutingProduct.fixedSubgroup
        (MulAut.conjNormal (H := normalSubgroup) element)),
      TwoComponents.IsTwoComponent fixedComponent ∧ ¬ IsQuasisimple fixedComponent ∧
        (fixedComponent.map (FixedCommutingProduct.fixedSubgroup
          (MulAut.conjNormal (H := normalSubgroup) element)).subtype).map normalSubgroup.subtype =
            localComponent.map (Subgroup.centralizer ({element} : Set G)).subtype := by
  let centralizer := Subgroup.centralizer ({element} : Set G)
  let localNormal := normalSubgroup.subgroupOf centralizer
  have hlocalLe : localComponent ≤ localNormal := by
    intro member hmember
    exact hcontained (Subgroup.mem_map_of_mem centralizer.subtype hmember)
  let restricted := localComponent.subgroupOf localNormal
  let fixedEquivalence := equivalence normalSubgroup element
  let image := restricted.map fixedEquivalence.toMonoidHom
  have hrestricted := TwoComponentTransport.of_overgroup hlocal hlocalLe
  have himage : TwoComponents.IsTwoComponent image :=
    (TwoComponentTransport.equiv_iff fixedEquivalence restricted).mpr hrestricted
  have hnotImage : ¬ IsQuasisimple image := by
    intro hquasi
    have hrestrictedQuasi := Components.quasisimple_of_equiv
      (restricted.equivMapOfInjective fixedEquivalence.toMonoidHom fixedEquivalence.injective) hquasi
    exact hnotQuasisimple (Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hlocalLe).symm hrestrictedQuasi)
  refine ⟨image, himage, hnotImage, ?_⟩
  have hcompatibility : (normalSubgroup.subtype.comp
      (FixedCommutingProduct.fixedSubgroup
        (MulAut.conjNormal (H := normalSubgroup) element)).subtype).comp fixedEquivalence.toMonoidHom =
          centralizer.subtype.comp localNormal.subtype := by
    ext member
    rfl
  change (restricted.map fixedEquivalence.toMonoidHom |>.map
    (FixedCommutingProduct.fixedSubgroup
      (MulAut.conjNormal (H := normalSubgroup) element)).subtype).map normalSubgroup.subtype = _
  rw [Subgroup.map_map, Subgroup.map_map, hcompatibility, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hlocalLe]

end CFSG.ComponentClassification.FixedNormalCentralizer
