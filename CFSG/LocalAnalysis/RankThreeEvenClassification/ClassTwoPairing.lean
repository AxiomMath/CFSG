module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

open scoped commutatorElement

local instance classTwoCenterCommGroup {G : Type u} [Group G] : CommGroup (Subgroup.center G) :=
  @IsMulCommutative.instCommGroup (Subgroup.center G) inferInstance inferInstance

theorem classTwo_commutator_mem_center {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first second : G) :
    ⁅first, second⁆ ∈ Subgroup.center G :=
  hclass (Subgroup.commutator_mem_commutator (Subgroup.mem_top first) (Subgroup.mem_top second))

theorem center_conjugate_eq {G : Type u} [Group G]
    (central element : G) (hcentral : central ∈ Subgroup.center G) :
    element * central * element⁻¹ = central := by
  rw [Subgroup.mem_center_iff.mp hcentral element, mul_assoc, mul_inv_cancel, mul_one]

theorem classTwo_commutator_mul_left {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first second third : G) :
    ⁅first * second, third⁆ = ⁅first, third⁆ * ⁅second, third⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    center_conjugate_eq _ _ (classTwo_commutator_mem_center hclass second third)]
  exact Subgroup.mem_center_iff.mp (classTwo_commutator_mem_center hclass first third) _

theorem classTwo_commutator_mul_right {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first second third : G) :
    ⁅first, second * third⁆ = ⁅first, second⁆ * ⁅first, third⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅first, second⁆ * second * ⁅first, third⁆ * second⁻¹ =
        ⁅first, second⁆ * (second * ⁅first, third⁆ * second⁻¹) := by group
    _ = ⁅first, second⁆ * ⁅first, third⁆ := by
      rw [center_conjugate_eq _ _ (classTwo_commutator_mem_center hclass first third)]

@[expose] def classTwoCommutatorHomRight {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first : G) : G →* Subgroup.center G where
  toFun second := ⟨⁅first, second⁆, classTwo_commutator_mem_center hclass first second⟩
  map_one' := Subtype.ext (commutatorElement_one_right first)
  map_mul' second third := Subtype.ext (classTwo_commutator_mul_right hclass first second third)

@[expose] def classTwoCommutatorHom {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) : G →* (G →* Subgroup.center G) where
  toFun first := classTwoCommutatorHomRight hclass first
  map_one' := by
    ext second
    exact commutatorElement_one_left second
  map_mul' first second := by
    ext third
    exact classTwo_commutator_mul_left hclass first second third

@[expose] def classTwoQuotientHom {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) : G →* (Abelianization G →* Subgroup.center G) where
  toFun first := Abelianization.lift (classTwoCommutatorHomRight hclass first)
  map_one' := by
    apply Abelianization.hom_ext
    ext second
    simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of, MonoidHom.one_apply]
    exact commutatorElement_one_left second
  map_mul' first second := by
    apply Abelianization.hom_ext
    ext third
    simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of, MonoidHom.mul_apply]
    exact classTwo_commutator_mul_left hclass first second third

@[expose] def classTwoAbelianPairing {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) :
    Abelianization G →* (Abelianization G →* Subgroup.center G) :=
  Abelianization.lift (classTwoQuotientHom hclass)

theorem classTwoAbelianPairing_apply {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first second : G) :
    (classTwoAbelianPairing hclass (Abelianization.of first) (Abelianization.of second) : G) =
      ⁅first, second⁆ := by
  simp only [classTwoAbelianPairing, Abelianization.lift_apply_of, classTwoQuotientHom,
    MonoidHom.coe_mk, OneHom.coe_mk, classTwoCommutatorHomRight]

theorem classTwoAbelianPairing_alternating {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (vector : Abelianization G) :
    classTwoAbelianPairing hclass vector vector = 1 := by
  refine QuotientGroup.induction_on vector ?_
  intro representative
  apply Subtype.ext
  exact (classTwoAbelianPairing_apply hclass representative representative).trans
    (commutatorElement_self representative)

theorem classTwoAbelianPairing_invariant {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (automorphism : MulAut G)
    (hfixed : ∀ element ∈ commutator G, automorphism element = element)
    (first second : Abelianization G) :
    classTwoAbelianPairing hclass (Abelianization.map automorphism.toMonoidHom first)
      (Abelianization.map automorphism.toMonoidHom second) = classTwoAbelianPairing hclass first second := by
  refine QuotientGroup.induction_on first ?_
  intro firstRepresentative
  refine QuotientGroup.induction_on second ?_
  intro secondRepresentative
  apply Subtype.ext
  change (classTwoAbelianPairing hclass
    (Abelianization.map automorphism.toMonoidHom (Abelianization.of firstRepresentative))
    (Abelianization.map automorphism.toMonoidHom (Abelianization.of secondRepresentative)) : G) =
      (classTwoAbelianPairing hclass (Abelianization.of firstRepresentative)
        (Abelianization.of secondRepresentative) : G)
  rw [Abelianization.map_of, Abelianization.map_of, classTwoAbelianPairing_apply,
    classTwoAbelianPairing_apply, ← map_commutatorElement]
  exact hfixed _ (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

@[expose] def classTwoAdditivePairing {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) :
    Additive (Abelianization G) →+ Additive (Abelianization G) →+ Additive (Subgroup.center G) where
  toFun first := MonoidHom.toAdditive (classTwoAbelianPairing hclass (Additive.toMul first))
  map_zero' := by
    apply AddMonoidHom.ext
    intro second
    change classTwoAbelianPairing hclass 1 (Additive.toMul second) = 1
    rw [map_one, MonoidHom.one_apply]
  map_add' first second := by
    apply AddMonoidHom.ext
    intro third
    change classTwoAbelianPairing hclass (Additive.toMul first * Additive.toMul second)
      (Additive.toMul third) =
      classTwoAbelianPairing hclass (Additive.toMul first) (Additive.toMul third) *
        classTwoAbelianPairing hclass (Additive.toMul second) (Additive.toMul third)
    rw [MonoidHom.map_mul₂]

theorem classTwoAdditivePairing_apply {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (first second : Additive (Abelianization G)) :
    classTwoAdditivePairing hclass first second =
      Additive.ofMul (classTwoAbelianPairing hclass (Additive.toMul first) (Additive.toMul second)) := rfl

theorem classTwoAdditivePairing_alternating {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (vector : Additive (Abelianization G)) :
    classTwoAdditivePairing hclass vector vector = 0 := by
  rw [classTwoAdditivePairing_apply, classTwoAbelianPairing_alternating]
  rfl

theorem classTwoAdditivePairing_invariant {G : Type u} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (automorphism : MulAut G)
    (hfixed : ∀ element ∈ commutator G, automorphism element = element)
    (first second : Additive (Abelianization G)) :
    classTwoAdditivePairing hclass
      (MonoidHom.toAdditive (Abelianization.map automorphism.toMonoidHom) first)
      (MonoidHom.toAdditive (Abelianization.map automorphism.toMonoidHom) second) =
      classTwoAdditivePairing hclass first second := by
  simp only [classTwoAdditivePairing_apply, MonoidHom.toAdditive_apply_apply]
  exact congrArg Additive.ofMul (classTwoAbelianPairing_invariant hclass automorphism hfixed _ _)

end CFSG.RankThreeEvenClassification.Helpers
