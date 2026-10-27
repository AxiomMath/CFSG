module

public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProduct

public section

namespace CFSG.ComponentClassification.NormalizedProductCentralizer

theorem centralizer_le {G : Type*} [Group G] (normal acting intersection : Subgroup G)
    (hnormalizes : acting ≤ Subgroup.normalizer (normal : Set G))
    (element : G) (hcentral : acting ≤ Subgroup.centralizer {element})
    (hcentralizer : Subgroup.centralizer {element} ⊓ normal ≤ intersection) :
    Subgroup.centralizer {element} ⊓ (normal ⊔ acting) ≤ intersection ⊔ acting := by
  intro member hmember
  obtain ⟨left, hleft, right, hright, heq⟩ := NormalizedProduct.coordinates normal acting hnormalizes
    member hmember.2
  have hleftCentral : left ∈ Subgroup.centralizer {element} := by
    have hmem := (Subgroup.centralizer {element}).mul_mem hmember.1
      ((Subgroup.centralizer {element}).inv_mem (hcentral hright))
    rw [← heq, mul_inv_cancel_right] at hmem
    exact hmem
  rw [← heq]
  exact Subgroup.mul_mem_sup (hcentralizer ⟨hleftCentral, hleft⟩) hright

end CFSG.ComponentClassification.NormalizedProductCentralizer
