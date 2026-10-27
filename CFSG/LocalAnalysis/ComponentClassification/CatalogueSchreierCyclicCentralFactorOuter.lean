module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCyclicCentralFactorAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor

open OuterAutomorphisms

variable {L Z : Type*} [Group L] [Group Z]

theorem productAutomorphismHom_conj [IsMulCommutative Z] (left : L) (right : Z) :
    productAutomorphismHom (MulAut.conj left, (1 : MulAut Z)) =
      MulAut.conj (left, right) := by
  apply MulEquiv.ext
  rintro ⟨otherLeft, otherRight⟩
  apply Prod.ext
  · rfl
  · change otherRight = right * otherRight * right⁻¹
    have hcomm : right * otherRight = otherRight * right :=
      isMulCommutative_iff.mp (inferInstance : IsMulCommutative Z) right otherRight
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem product_inner_image [IsMulCommutative Z] :
    ((inner L).prod (⊥ : Subgroup (MulAut Z))).map productAutomorphismHom =
      inner (L × Z) := by
  apply le_antisymm
  · rintro _ ⟨⟨left, right⟩, hmember, rfl⟩
    obtain ⟨element, rfl⟩ := hmember.1
    have hright : right = 1 := Subgroup.mem_bot.mp hmember.2
    rw [hright, productAutomorphismHom_conj (Z := Z) element (1 : Z)]
    exact ⟨(element, 1), rfl⟩
  · rintro _ ⟨⟨left, right⟩, rfl⟩
    exact ⟨(MulAut.conj left, 1), ⟨⟨left, rfl⟩, Subgroup.one_mem _⟩,
      productAutomorphismHom_conj left right⟩

theorem restriction_inner_image [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) :
    (inner (L × Z)).map (automorphismEquivalence hcenter).toMonoidHom =
      (inner L).prod (⊥ : Subgroup (MulAut Z)) := by
  rw [← product_inner_image, Subgroup.map_map]
  have hcomp : (automorphismEquivalence (Z := Z) hcenter).toMonoidHom.comp
      (productAutomorphismHom (L := L) (Z := Z)) =
        MonoidHom.id (MulAut L × MulAut Z) := by
    apply MonoidHom.ext
    intro pair
    exact (MulEquiv.ofBijective productAutomorphismHom
      ⟨productAutomorphismHom_injective, productAutomorphismHom_surjective hcenter⟩).symm_apply_apply pair
  rw [hcomp, Subgroup.map_id]

@[expose] noncomputable def outerEquivalence [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥) : Outer (L × Z) ≃* Outer L × MulAut Z :=
  (QuotientGroup.congr (inner (L × Z)) ((inner L).prod (⊥ : Subgroup (MulAut Z)))
    (automorphismEquivalence hcenter) (restriction_inner_image hcenter)).trans
    ((QuotientGroup.prodMulEquiv (inner L) (⊥ : Subgroup (MulAut Z))).trans
      ((MulEquiv.refl (Outer L)).prodCongr QuotientGroup.quotientBot))

theorem outer_solvable [Group.IsPerfect L] [IsMulCommutative Z]
    (hcenter : Subgroup.center L = ⊥)
    [Group.IsSolvable (Outer L)] [Group.IsSolvable (MulAut Z)] :
    Group.IsSolvable (Outer (L × Z)) :=
  Group.isSolvable_of_surjective
    (f := (outerEquivalence (Z := Z) hcenter).symm.toMonoidHom)
    (outerEquivalence (Z := Z) hcenter).symm.surjective

theorem outer_solvable_of_cyclic [Group.IsPerfect L] [IsCyclic Z]
    (hcenter : Subgroup.center L = ⊥) [Group.IsSolvable (Outer L)] :
    Group.IsSolvable (Outer (L × Z)) := by
  let : Group.IsSolvable (MulAut Z) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv Z).toMonoidHom)
      (IsCyclic.mulAutMulEquiv Z).injective
  exact outer_solvable hcenter

end CFSG.ComponentClassification.CatalogueSchreierCyclicCentralFactor
