module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.PerfectKernelActions

public section

namespace CFSG.ComponentClassification.FixedCentralPreimage

@[expose] noncomputable def subgroup {G : Type*} [Group G] (automorphism : MulAut G) : Subgroup G :=
  (FixedCommutingProduct.fixedSubgroup (PerfectAutomorphisms.onCenterQuotient automorphism)).comap
    (QuotientGroup.mk' (Subgroup.center G))

theorem mem_iff {G : Type*} [Group G] (automorphism : MulAut G) (element : G) :
    element ∈ subgroup automorphism ↔ element⁻¹ * automorphism element ∈ Subgroup.center G := by
  let projection := QuotientGroup.mk' (Subgroup.center G)
  change PerfectAutomorphisms.onCenterQuotient automorphism (projection element) = projection element ↔
    element⁻¹ * automorphism element ∈ Subgroup.center G
  rw [PerfectAutomorphisms.onCenterQuotient_apply_mk]
  constructor
  · intro heq
    apply (QuotientGroup.eq_one_iff _).mp
    change projection (element⁻¹ * automorphism element) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  · intro hmem
    have hone := (QuotientGroup.eq_one_iff _).mpr hmem
    change projection (element⁻¹ * automorphism element) = 1 at hone
    rw [map_mul, map_inv] at hone
    exact (inv_mul_eq_one.mp hone).symm

@[expose] def displacement {G : Type*} [Group G] (automorphism : MulAut G) :
    subgroup automorphism →* Subgroup.center G :=
  { toFun := fun element => ⟨element.val⁻¹ * automorphism element.val,
      (mem_iff automorphism element.val).mp element.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro left right
      apply Subtype.ext
      have hcentral := Subgroup.mem_center_iff.mp
        ((mem_iff automorphism left.val).mp left.property) right.val
      change (left.val * right.val)⁻¹ * automorphism (left.val * right.val) =
        (left.val⁻¹ * automorphism left.val) * (right.val⁻¹ * automorphism right.val)
      rw [map_mul]
      calc
        (left.val * right.val)⁻¹ * (automorphism left.val * automorphism right.val) =
            right.val⁻¹ * (left.val⁻¹ * automorphism left.val) * automorphism right.val := by group
        _ = (left.val⁻¹ * automorphism left.val) * right.val⁻¹ * automorphism right.val := by
          have hcentralInv := Subgroup.mem_center_iff.mp
            ((mem_iff automorphism left.val).mp left.property) right.val⁻¹
          rw [hcentralInv]
        _ = (left.val⁻¹ * automorphism left.val) * (right.val⁻¹ * automorphism right.val) :=
          mul_assoc _ _ _ }

theorem displacement_eq_one_iff {G : Type*} [Group G]
    (automorphism : MulAut G) (element : subgroup automorphism) :
    displacement automorphism element = 1 ↔ automorphism element.val = element.val := by
  constructor
  · intro hone
    have hvalue : element.val⁻¹ * automorphism element.val = 1 := congrArg Subtype.val hone
    exact (inv_mul_eq_one.mp hvalue).symm
  · intro hfixed
    apply Subtype.ext
    change element.val⁻¹ * automorphism element.val = 1
    rw [hfixed, inv_mul_cancel]

theorem fixed_of_perfect_action {A G : Type*} [Group A] [Group.IsPerfect A] [Group G]
    (action : A →* MulAut G) (automorphism : MulAut G)
    (hcommutes : ∀ actor : A, Commute automorphism (action actor))
    (hcenter : ∀ actor : A, ∀ member ∈ Subgroup.center G, (action actor) member = member)
    (hfixed : ∀ actor : A, ∀ member : G, automorphism member = member →
      (action actor) member = member) :
    ∀ actor : A, ∀ member ∈ subgroup automorphism, (action actor) member = member := by
  have hdisplacement : ∀ actor : A, ∀ member ∈ subgroup automorphism,
      ((action actor) member)⁻¹ * automorphism ((action actor) member) =
        member⁻¹ * automorphism member := by
    intro actor member hmem
    have hcommutation := congrArg (fun transformation : MulAut G => transformation member)
      (hcommutes actor).eq
    change automorphism ((action actor) member) = (action actor) (automorphism member) at hcommutation
    rw [hcommutation, ← map_inv, ← map_mul]
    exact hcenter actor _ ((mem_iff automorphism member).mp hmem)
  have hinvariant : ∀ actor : A, (subgroup automorphism).map (action actor).toMonoidHom =
      subgroup automorphism := by
    intro actor
    apply le_antisymm
    · rintro member ⟨lift, hmem, rfl⟩
      apply (mem_iff automorphism _).mpr
      change ((action actor) lift)⁻¹ * automorphism ((action actor) lift) ∈ Subgroup.center G
      rw [hdisplacement actor lift hmem]
      exact (mem_iff automorphism lift).mp hmem
    · intro member hmem
      have hinverse : (action actor⁻¹) member ∈ subgroup automorphism := by
        apply (mem_iff automorphism _).mpr
        rw [hdisplacement actor⁻¹ member hmem]
        exact (mem_iff automorphism member).mp hmem
      refine ⟨(action actor⁻¹) member, hinverse, ?_⟩
      rw [map_inv]
      exact (action actor).apply_symm_apply member
  let restrictedAction : A →* MulAut (subgroup automorphism) :=
    { toFun := fun actor => ((action actor).subgroupMap (subgroup automorphism)).trans
        (MulEquiv.subgroupCongr (hinvariant actor))
      map_one' := by
        apply MulEquiv.ext
        intro member
        apply Subtype.ext
        change (action 1) member.val = member.val
        rw [map_one]
        rfl
      map_mul' := by
        intro left right
        apply MulEquiv.ext
        intro member
        apply Subtype.ext
        change (action (left * right)) member.val = (action left) ((action right) member.val)
        rw [map_mul]
        rfl }
  have hrestrictedTrivial := PerfectKernelActions.action_eq_one_of_fixed_kernel
    (displacement automorphism) restrictedAction
    (fun actor member => Subtype.ext (hdisplacement actor member.val member.property))
    (by
      intro actor member hmem
      apply Subtype.ext
      exact hfixed actor member.val ((displacement_eq_one_iff automorphism member).mp hmem))
  intro actor member hmem
  have hvalue := congrArg (fun homomorphism : A →* MulAut (subgroup automorphism) =>
    ((homomorphism actor) (⟨member, hmem⟩ : subgroup automorphism)).val) hrestrictedTrivial
  exact hvalue

theorem ambient_centralization {G : Type*} [Group G]
    (normalSubgroup perfectSubgroup : Subgroup G) [normalSubgroup.Normal]
    [Group.IsPerfect perfectSubgroup] (element : G)
    (hcentralizesElement : perfectSubgroup ≤ Subgroup.centralizer ({element} : Set G))
    (hcentralizesCenter : ⁅perfectSubgroup, (Subgroup.center normalSubgroup).map
      normalSubgroup.subtype⁆ = ⊥)
    (hcentralizesFixed : ⁅perfectSubgroup,
      normalSubgroup ⊓ Subgroup.centralizer ({element} : Set G)⁆ = ⊥) :
    ⁅perfectSubgroup, (subgroup (MulAut.conjNormal element : MulAut normalSubgroup)).map
      normalSubgroup.subtype⁆ = ⊥ := by
  let automorphism : MulAut normalSubgroup := MulAut.conjNormal element
  let action : perfectSubgroup →* MulAut normalSubgroup :=
    (MulAut.conjNormal : G →* MulAut normalSubgroup).comp perfectSubgroup.subtype
  have hcommutes : ∀ actor : perfectSubgroup, Commute automorphism (action actor) := by
    intro actor
    have heq := Subgroup.mem_centralizer_iff.mp (hcentralizesElement actor.property) element
      (Set.mem_singleton element)
    exact (show Commute element actor.val from heq).map
      (MulAut.conjNormal : G →* MulAut normalSubgroup)
  have hcenter : ∀ actor : perfectSubgroup, ∀ member ∈ Subgroup.center normalSubgroup,
      (action actor) member = member := by
    intro actor member hmember
    have hmem := Subgroup.mem_map_of_mem normalSubgroup.subtype hmember
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizesCenter actor.property)
        member.val hmem
    apply Subtype.ext
    change actor.val * member.val * actor.val⁻¹ = member.val
    rw [← heq]
    group
  have hfixed : ∀ actor : perfectSubgroup, ∀ member : normalSubgroup,
      automorphism member = member → (action actor) member = member := by
    intro actor member hmember
    have hvalue : element * member.val * element⁻¹ = member.val := congrArg Subtype.val hmember
    have hcentralizer : member.val ∈ Subgroup.centralizer ({element} : Set G) := by
      apply Subgroup.mem_centralizer_iff.mpr
      intro singleton hsingleton
      rw [Set.mem_singleton_iff.mp hsingleton]
      calc
        element * member.val = (element * member.val * element⁻¹) * element := by group
        _ = member.val * element := by rw [hvalue]
    have heq := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentralizesFixed actor.property)
        member.val ⟨member.property, hcentralizer⟩
    apply Subtype.ext
    change actor.val * member.val * actor.val⁻¹ = member.val
    rw [← heq]
    group
  have hfull := fixed_of_perfect_action action automorphism hcommutes hcenter hfixed
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro actor hactor
  apply Subgroup.mem_centralizer_iff.mpr
  intro member hmember
  obtain ⟨lift, hlift, rfl⟩ := Subgroup.mem_map.mp hmember
  have hvalue := congrArg Subtype.val (hfull (⟨actor, hactor⟩ : perfectSubgroup) lift hlift)
  change actor * lift.val * actor⁻¹ = lift.val at hvalue
  calc
    lift.val * actor = (actor * lift.val * actor⁻¹) * actor := by rw [hvalue]
    _ = actor * lift.val := by group

end CFSG.ComponentClassification.FixedCentralPreimage
