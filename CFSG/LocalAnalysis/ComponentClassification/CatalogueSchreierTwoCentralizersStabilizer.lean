module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

open OuterAutomorphisms

variable {G : Type*} [Group G]

@[expose] def stabilizer (M : Subgroup G) : Subgroup (MulAut G) where
  carrier := {automorphism | ∀ member, member ∈ M ↔ automorphism member ∈ M}
  one_mem' _ := Iff.rfl
  mul_mem' hleft hright member :=
    (hright member).trans (hleft _)
  inv_mem' {automorphism} hautomorphism member := by
    have h := hautomorphism (automorphism.symm member)
    rw [automorphism.apply_symm_apply] at h
    exact h.symm

theorem mem_stabilizer_iff_map (M : Subgroup G) (automorphism : MulAut G) :
    automorphism ∈ stabilizer M ↔ M.map automorphism.toMonoidHom = M := by
  constructor
  · intro hautomorphism
    ext member
    constructor
    · rintro ⟨lift, hlift, rfl⟩
      exact (hautomorphism lift).mp hlift
    · intro hmember
      refine ⟨automorphism.symm member, ?_, automorphism.apply_symm_apply member⟩
      have hfixedImage : automorphism (automorphism.symm member) ∈ M := by
        simpa only [MulEquiv.apply_symm_apply] using hmember
      exact (hautomorphism (automorphism.symm member)).mpr hfixedImage
  · intro hmap member
    constructor
    · intro hmember
      rw [← hmap]
      exact Subgroup.mem_map_of_mem automorphism.toMonoidHom hmember
    · intro hmember
      rw [← hmap] at hmember
      obtain ⟨lift, hlift, heq⟩ := hmember
      have hsame := automorphism.injective heq
      exact hsame ▸ hlift

@[expose] def restrict (M : Subgroup G) : stabilizer M →* MulAut M where
  toFun automorphism :=
    { toFun := fun member => ⟨(automorphism : MulAut G) member,
        (automorphism.property member).mp member.property⟩
      invFun := fun member => ⟨(automorphism : MulAut G).symm member, by
        apply (automorphism.property _).mpr
        simpa only [MulEquiv.apply_symm_apply] using member.property⟩
      left_inv member := Subtype.ext ((automorphism : MulAut G).symm_apply_apply member)
      right_inv member := Subtype.ext ((automorphism : MulAut G).apply_symm_apply member)
      map_mul' left right := Subtype.ext ((automorphism : MulAut G).map_mul left right) }
  map_one' := by ext member; rfl
  map_mul' _ _ := by ext member; rfl

theorem restrict_apply_val (M : Subgroup G) (automorphism : stabilizer M) (member : M) :
    (restrict M automorphism member).val = (automorphism : MulAut G) member := rfl

@[expose] def pointwiseKernel (M : Subgroup G) : Subgroup (stabilizer M) := (restrict M).ker

theorem pointwiseKernel_fixes (M : Subgroup G) (automorphism : pointwiseKernel M)
    (member : G) (hmember : member ∈ M) :
    ((automorphism : stabilizer M) : MulAut G) member = member :=
  congrArg (fun action : MulAut M => (action (⟨member, hmember⟩ : M)).val)
    automorphism.property

@[expose] def subgroupInnerHom (M : Subgroup G) : M →* stabilizer M :=
  ((MulAut.conj : G →* MulAut G).comp M.subtype).codRestrict (stabilizer M) (by
    intro actor
    change ∀ member, member ∈ M ↔ actor.val * member * actor.val⁻¹ ∈ M
    intro member
    constructor
    · intro hmember
      exact M.mul_mem (M.mul_mem actor.property hmember) (M.inv_mem actor.property)
    · intro hmember
      have h := M.mul_mem (M.mul_mem (M.inv_mem actor.property) hmember) actor.property
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right,
        inv_mul_cancel, mul_one] using h)

@[expose] def subgroupInner (M : Subgroup G) : Subgroup (stabilizer M) :=
  (subgroupInnerHom M).range

theorem restrict_subgroupInnerHom (M : Subgroup G) (member : M) :
    restrict M (subgroupInnerHom M member) = MulAut.conj member := by
  apply MulEquiv.ext
  intro other
  apply Subtype.ext
  rfl

theorem subgroupInner_normal (M : Subgroup G) : (subgroupInner M).Normal := by
  constructor
  intro automorphism hautomorphism actor
  obtain ⟨member, rfl⟩ := hautomorphism
  refine ⟨restrict M actor member, ?_⟩
  apply Subtype.ext
  apply MulEquiv.ext
  intro other
  change (actor : MulAut G) member * other * ((actor : MulAut G) member)⁻¹ =
    (actor : MulAut G) (member.val * (actor : MulAut G).symm other * member.val⁻¹)
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

instance subgroupInnerNormal (M : Subgroup G) : (subgroupInner M).Normal :=
  subgroupInner_normal M

@[expose] noncomputable def restrictionOuterHom (M : Subgroup G) : stabilizer M →* Outer M :=
  (QuotientGroup.mk' (inner M)).comp (restrict M)

theorem restrictionOuterHom_ker (M : Subgroup G) :
    (restrictionOuterHom M).ker = pointwiseKernel M ⊔ subgroupInner M := by
  apply le_antisymm
  · intro automorphism hautomorphism
    have hinner : restrict M automorphism ∈ inner M :=
      (QuotientGroup.eq_one_iff _).mp hautomorphism
    obtain ⟨member, hmember⟩ := hinner
    let fixing := automorphism * (subgroupInnerHom M member)⁻¹
    have hfixing : fixing ∈ pointwiseKernel M := by
      change restrict M (automorphism * (subgroupInnerHom M member)⁻¹) = 1
      rw [map_mul, map_inv, restrict_subgroupInnerHom, hmember, mul_inv_cancel]
    have hproduct : fixing * subgroupInnerHom M member = automorphism := by
      dsimp [fixing]
      group
    rw [← hproduct]
    exact Subgroup.mul_mem_sup hfixing ⟨member, rfl⟩
  · apply sup_le
    · intro automorphism hautomorphism
      change QuotientGroup.mk' (inner M) (restrict M automorphism) = 1
      rw [show restrict M automorphism = 1 from hautomorphism, map_one]
    · rintro _ ⟨member, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨member, (restrict_subgroupInnerHom M member).symm⟩

noncomputable abbrev InnerQuotient (M : Subgroup G) := stabilizer M ⧸ subgroupInner M

@[expose] noncomputable def innerQuotientRestriction (M : Subgroup G) :
    InnerQuotient M →* Outer M :=
  QuotientGroup.lift (subgroupInner M) (restrictionOuterHom M) (by
    rw [restrictionOuterHom_ker]
    exact le_sup_right)

@[expose] def pointwiseQuotientHom (M : Subgroup G) : pointwiseKernel M →* InnerQuotient M :=
  (QuotientGroup.mk' (subgroupInner M)).comp (pointwiseKernel M).subtype

theorem innerQuotientRestriction_ker (M : Subgroup G) :
    (innerQuotientRestriction M).ker = (pointwiseQuotientHom M).range := by
  apply le_antisymm
  · intro member hmember
    obtain ⟨automorphism, rfl⟩ := QuotientGroup.mk'_surjective (subgroupInner M) member
    have hrestriction : automorphism ∈ (restrictionOuterHom M).ker := hmember
    rw [restrictionOuterHom_ker] at hrestriction
    obtain ⟨fixing, hfixing, innerElement, hinnerElement, heq⟩ :=
      Subgroup.mem_sup_of_normal_right.mp hrestriction
    refine ⟨⟨fixing, hfixing⟩, ?_⟩
    change QuotientGroup.mk' (subgroupInner M) fixing =
      QuotientGroup.mk' (subgroupInner M) automorphism
    have hone : QuotientGroup.mk' (subgroupInner M) innerElement = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hinnerElement
    rw [← heq, map_mul, hone, mul_one]
  · rintro _ ⟨automorphism, rfl⟩
    change restrictionOuterHom M automorphism.val = 1
    change QuotientGroup.mk' (inner M) (restrict M automorphism.val) = 1
    rw [show restrict M automorphism.val = 1 from automorphism.property, map_one]

theorem innerQuotient_solvable (M : Subgroup G)
    [Group.IsSolvable (pointwiseKernel M)] [Group.IsSolvable (Outer M)] :
    Group.IsSolvable (InnerQuotient M) := by
  apply Group.isSolvable_of_ker_le_range (pointwiseQuotientHom M) (innerQuotientRestriction M)
  exact (innerQuotientRestriction_ker M).le

end CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers
