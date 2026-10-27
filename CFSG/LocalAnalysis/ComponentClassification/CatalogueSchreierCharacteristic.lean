module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierCharacteristicKernel
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueSchreierCharacteristic

open CFSG.FiveTransitive.CharacteristicAutomorphism
open OuterAutomorphisms (inner Outer)

variable {H : Type*} [Group H]

@[expose] def innerSubgroup (D : Subgroup H) : Subgroup (MulAut H) :=
  ((MulAut.conj : H →* MulAut H).comp D.subtype).range

theorem innerSubgroup_normal (D : Subgroup H) [D.Characteristic] :
    (innerSubgroup D).Normal := by
  constructor
  intro automorphism hautomorphism conjugator
  obtain ⟨element, rfl⟩ := hautomorphism
  refine ⟨⟨conjugator element, mem D conjugator element.property⟩, ?_⟩
  apply MulEquiv.ext
  intro member
  change conjugator element * member * (conjugator element)⁻¹ =
    conjugator (element * conjugator.symm member * (element : H)⁻¹)
  rw [map_mul, map_mul, map_inv, conjugator.apply_symm_apply]

instance innerSubgroupNormal (D : Subgroup H) [D.Characteristic] :
    (innerSubgroup D).Normal := innerSubgroup_normal D

theorem innerSubgroup_le_inner (D : Subgroup H) : innerSubgroup D ≤ inner H := by
  rintro automorphism ⟨element, rfl⟩
  exact ⟨(element : H), rfl⟩

theorem restrict_conj (D : Subgroup H) [D.Characteristic] (element : D) :
    restrict D (MulAut.conj (element : H)) = MulAut.conj element := by
  apply MulEquiv.ext
  intro member
  apply Subtype.ext
  rfl

theorem innerSubgroup_le_restrictionInner (D : Subgroup H) [D.Characteristic] :
    innerSubgroup D ≤ (inner D).comap (restrict D) := by
  rintro automorphism ⟨element, rfl⟩
  exact ⟨element, (restrict_conj D element).symm⟩

@[expose] def restrictionOuterHom (D : Subgroup H) [D.Characteristic] :
    MulAut H →* Outer D := (QuotientGroup.mk' (inner D)).comp (restrict D)

theorem restrictionOuterHom_ker (D : Subgroup H) [D.Characteristic] :
    (restrictionOuterHom D).ker = (inner D).comap (restrict D) := by
  ext automorphism
  exact QuotientGroup.eq_one_iff (restrict D automorphism)

theorem restrictionOuterHom_ker_eq_sup (D : Subgroup H) [D.Characteristic] :
    (restrictionOuterHom D).ker = pointwiseKernel D ⊔ innerSubgroup D := by
  rw [restrictionOuterHom_ker]
  apply le_antisymm
  · intro automorphism hautomorphism
    obtain ⟨element, helement⟩ := hautomorphism
    let fixing := automorphism * (MulAut.conj (element : H))⁻¹
    have hfixing : fixing ∈ pointwiseKernel D := by
      change restrict D (automorphism * (MulAut.conj (element : H))⁻¹) = 1
      rw [map_mul, map_inv, restrict_conj, ← helement, mul_inv_cancel]
    have hinner : MulAut.conj (element : H) ∈ innerSubgroup D := ⟨element, rfl⟩
    have hproduct : fixing * MulAut.conj (element : H) = automorphism := by
      dsimp [fixing]
      group
    rw [← hproduct]
    exact (pointwiseKernel D ⊔ innerSubgroup D).mul_mem
      (Subgroup.mem_sup_left hfixing) (Subgroup.mem_sup_right hinner)
  · apply sup_le
    · intro automorphism hautomorphism
      have hrestriction : restrict D automorphism = 1 := hautomorphism
      change restrict D automorphism ∈ OuterAutomorphisms.inner D
      rw [hrestriction]
      exact (inner D).one_mem
    · exact innerSubgroup_le_restrictionInner D

abbrev innerQuotient (D : Subgroup H) [D.Characteristic] :=
  MulAut H ⧸ innerSubgroup D

@[expose] def innerQuotientRestriction (D : Subgroup H) [D.Characteristic] :
    innerQuotient D →* Outer D :=
  QuotientGroup.map (innerSubgroup D) (inner D) (restrict D)
    (innerSubgroup_le_restrictionInner D)

@[expose] def pointwiseKernelQuotientHom (D : Subgroup H) [D.Characteristic] :
    pointwiseKernel D →* innerQuotient D :=
  (QuotientGroup.mk' (innerSubgroup D)).comp (pointwiseKernel D).subtype

theorem innerQuotientRestriction_ker_eq_image (D : Subgroup H) [D.Characteristic] :
    (innerQuotientRestriction D).ker = (pointwiseKernelQuotientHom D).range := by
  apply le_antisymm
  · intro member hmember
    obtain ⟨automorphism, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup D) member
    have hinner : restrict D automorphism ∈ inner D :=
      (QuotientGroup.eq_one_iff _).mp hmember
    obtain ⟨element, helement⟩ := hinner
    let fixing := automorphism * (MulAut.conj (element : H))⁻¹
    have hfixing : fixing ∈ pointwiseKernel D := by
      change restrict D (automorphism * (MulAut.conj (element : H))⁻¹) = 1
      rw [map_mul, map_inv, restrict_conj, ← helement, mul_inv_cancel]
    refine ⟨⟨fixing, hfixing⟩, ?_⟩
    change (QuotientGroup.mk' (innerSubgroup D))
      (automorphism * (MulAut.conj (element : H))⁻¹) =
        (QuotientGroup.mk' (innerSubgroup D)) automorphism
    have hone : (QuotientGroup.mk' (innerSubgroup D)) (MulAut.conj (element : H)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨element, rfl⟩
    rw [map_mul, map_inv, hone, inv_one, mul_one]
  · rintro member ⟨automorphism, rfl⟩
    change (QuotientGroup.mk' (inner D)) (restrict D (automorphism : MulAut H)) = 1
    have hrestriction : restrict D (automorphism : MulAut H) = 1 := automorphism.property
    rw [hrestriction, map_one]

theorem innerQuotientRestriction_ker_isMulCommutative (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    IsMulCommutative (innerQuotientRestriction D).ker := by
  apply isMulCommutative_iff.mpr
  intro left right
  have hleft := (innerQuotientRestriction_ker_eq_image D).le left.property
  have hright := (innerQuotientRestriction_ker_eq_image D).le right.property
  obtain ⟨leftLift, hleftLift⟩ := hleft
  obtain ⟨rightLift, hrightLift⟩ := hright
  apply Subtype.ext
  change (left : innerQuotient D) * (right : innerQuotient D) =
    (right : innerQuotient D) * (left : innerQuotient D)
  rw [← hleftLift, ← hrightLift, ← map_mul, ← map_mul,
    pointwiseKernel_mul_comm D hcentralizer]

@[expose] def innerQuotientKernelEmbedding (D : Subgroup H) [D.Characteristic] :
    innerQuotient D ⧸ (innerQuotientRestriction D).ker →* Outer D :=
  QuotientGroup.kerLift (innerQuotientRestriction D)

theorem innerQuotientKernelEmbedding_injective (D : Subgroup H) [D.Characteristic] :
    Function.Injective (innerQuotientKernelEmbedding D) :=
  QuotientGroup.kerLift_injective (innerQuotientRestriction D)

theorem innerQuotient_solvable (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D)
    (houter : Group.IsSolvable (Outer D)) : Group.IsSolvable (innerQuotient D) := by
  let : IsMulCommutative (innerQuotientRestriction D).ker :=
    innerQuotientRestriction_ker_isMulCommutative D hcentralizer
  let : Group.IsSolvable (Outer D) := houter
  let : Group.IsSolvable (innerQuotient D ⧸ (innerQuotientRestriction D).ker) :=
    Group.isSolvable_of_isSolvable_injective (innerQuotientKernelEmbedding_injective D)
  exact Group.isSolvable_of_subgroup_quotient (innerQuotientRestriction D).ker

@[expose] def innerQuotientOuterHom (D : Subgroup H) [D.Characteristic] :
    innerQuotient D →* Outer H :=
  QuotientGroup.map (innerSubgroup D) (inner H) (MonoidHom.id (MulAut H))
    (innerSubgroup_le_inner D)

theorem innerQuotientOuterHom_surjective (D : Subgroup H) [D.Characteristic] :
    Function.Surjective (innerQuotientOuterHom D) := by
  intro member
  obtain ⟨automorphism, rfl⟩ := QuotientGroup.mk'_surjective (inner H) member
  exact ⟨(QuotientGroup.mk' (innerSubgroup D)) automorphism, rfl⟩

theorem outer_solvable (D : Subgroup H) [D.Characteristic]
    (hcentralizer : Subgroup.centralizer (D : Set H) ≤ D) :
    Group.IsSolvable (OuterAutomorphisms.Outer D) →
      Group.IsSolvable (OuterAutomorphisms.Outer H) := by
  intro houter
  let : Group.IsSolvable (innerQuotient D) := innerQuotient_solvable D hcentralizer houter
  exact Group.isSolvable_of_surjective (innerQuotientOuterHom_surjective D)

end CFSG.ComponentClassification.CatalogueSchreierCharacteristic
