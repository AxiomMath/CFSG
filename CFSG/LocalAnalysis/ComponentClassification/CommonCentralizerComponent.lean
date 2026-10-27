module

public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentTransport

public section

open CFSG.Open

namespace CFSG.ComponentClassification.CommonCentralizerComponent

theorem normal_fixed_intersection {G : Type*} [Group G]
    (lower upper fixed : Subgroup G) (hle : lower ≤ upper)
    (hnormal : (lower.subgroupOf upper).Normal) :
    ((lower ⊓ fixed).subgroupOf (upper ⊓ fixed)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff (inf_le_inf_right fixed hle)).mpr
  intro member actor hmember hactor
  exact ⟨(Subgroup.normal_subgroupOf_iff hle).mp hnormal member actor hmember.1 hactor.1,
    fixed.mul_mem (fixed.mul_mem hactor.2 hmember.2) (fixed.inv_mem hactor.2)⟩

theorem derived_component {G : Type*} [Group G]
    (product generated overgroup firstFixed secondFixed : Subgroup G)
    (hproduct : product ≤ generated) (hgenerated : generated ≤ overgroup)
    (hproductNormal : (product.subgroupOf generated).Normal)
    (hgeneratedNormal : (generated.subgroupOf overgroup).Normal)
    (hfirstFixed : firstFixed ≤ overgroup) (hproductFixed : product ≤ firstFixed)
    (component : Subgroup G) (hquasisimple : IsQuasisimple component)
    (hderived : ⁅product ⊓ secondFixed, product ⊓ secondFixed⁆ = component) :
    IsComponentOf (component.subgroupOf (firstFixed ⊓ secondFixed)) ⊤ := by
  let productFixed := product ⊓ secondFixed
  let middle := (generated ⊓ firstFixed) ⊓ secondFixed
  let common := firstFixed ⊓ secondFixed
  have hproductFixedLe : productFixed ≤ middle :=
    le_inf (le_inf (inf_le_left.trans hproduct) (inf_le_left.trans hproductFixed)) inf_le_right
  have hmiddleLe : middle ≤ common := inf_le_inf_right secondFixed inf_le_right
  have hproductNormalRestricted : (product.subgroupOf (generated ⊓ firstFixed)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    let : (product.subgroupOf generated).Normal := hproductNormal
    exact inf_le_left.trans (Subgroup.le_normalizer_of_normal_subgroupOf hproduct)
  have hproductMiddleNormal : (productFixed.subgroupOf middle).Normal :=
    normal_fixed_intersection product (generated ⊓ firstFixed) secondFixed
      (le_inf hproduct hproductFixed) hproductNormalRestricted
  have hgeneratedFirstNormal : ((generated ⊓ firstFixed).subgroupOf firstFixed).Normal := by
    have hnormal := normal_fixed_intersection generated overgroup firstFixed hgenerated hgeneratedNormal
    rwa [inf_eq_right.mpr hfirstFixed] at hnormal
  have hmiddleNormal : (middle.subgroupOf common).Normal :=
    normal_fixed_intersection (generated ⊓ firstFixed) firstFixed secondFixed inf_le_right hgeneratedFirstNormal
  have hcomponentLe : component ≤ productFixed := by
    rw [← hderived]
    exact Subgroup.commutator_le_self _
  have hcomponentNormal : (component.subgroupOf productFixed).Normal := by
    have hnormal : (⁅productFixed, productFixed⁆.subgroupOf (productFixed ⊔ productFixed)).Normal := inferInstance
    rw [show productFixed ⊔ productFixed = productFixed from sup_idem productFixed] at hnormal
    change (⁅product ⊓ secondFixed, product ⊓ secondFixed⁆.subgroupOf productFixed).Normal at hnormal
    rwa [hderived] at hnormal
  have hcomponentProduct : IsComponentOf (component.subgroupOf productFixed) ⊤ := by
    apply (OrdinaryComponentTransport.subgroupOf_iff component productFixed hcomponentLe).mpr
    exact ⟨hcomponentNormal.isSubnormal, hquasisimple⟩
  have hcomponentMiddle := OrdinaryComponentTransport.extend_nested component productFixed middle
    hcomponentLe hproductFixedLe hproductMiddleNormal.isSubnormal hcomponentProduct
  exact OrdinaryComponentTransport.extend_nested component middle common
    (hcomponentLe.trans hproductFixedLe) hmiddleLe hmiddleNormal.isSubnormal hcomponentMiddle

end CFSG.ComponentClassification.CommonCentralizerComponent
