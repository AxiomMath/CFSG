module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Assembly.OrderReductions.CoprimeFixedSubgroup
public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.Assembly.OrderReductions.InvariantQuotient
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.OrderReductions.ClassTwoCubic
public import CFSG.Assembly.OrderReductions.ActionPrimeCore

public section

namespace CFSG.OrderReductions.FrattiniAutomorphisms

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.ClassTwoCubic
open CFSG.OrderReductions.CoprimeFixedSubgroup CFSG.OrderReductions.FixedPointLifting

@[expose] def quotientEquivalence {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (automorphism : MulAut group) :
    MulAut (group ⧸ subgroup) :=
  QuotientGroup.congr subgroup subgroup automorphism
    (Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism)

theorem quotientEquivalence_apply {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic]
    (automorphism : MulAut group) (element : group) :
    quotientEquivalence subgroup automorphism (QuotientGroup.mk' subgroup element) =
      QuotientGroup.mk' subgroup (automorphism element) :=
  QuotientGroup.congr_mk' subgroup subgroup automorphism
    (Subgroup.characteristic_iff_map_eq.mp inferInstance automorphism) element

@[expose] def quotientAutomorphism {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] :
    MulAut group →* MulAut (group ⧸ subgroup) where
  toFun := quotientEquivalence subgroup
  map_one' := by
    ext element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
    change quotientEquivalence subgroup (1 : MulAut group)
      (QuotientGroup.mk' subgroup original) = QuotientGroup.mk' subgroup original
    rw [quotientEquivalence_apply]
    rfl
  map_mul' first second := by
    ext element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
    change quotientEquivalence subgroup (first * second)
        (QuotientGroup.mk' subgroup original) =
      quotientEquivalence subgroup first
        (quotientEquivalence subgroup second (QuotientGroup.mk' subgroup original))
    rw [quotientEquivalence_apply, quotientEquivalence_apply, quotientEquivalence_apply]
    rfl

theorem quotientAutomorphism_apply {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic]
    (automorphism : MulAut group) (element : group) :
    quotientAutomorphism subgroup automorphism (QuotientGroup.mk' subgroup element) =
      QuotientGroup.mk' subgroup (automorphism element) :=
  quotientEquivalence_apply subgroup automorphism element

@[expose] def quotientAction {actors group : Type*} [Group actors] [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (action : actors →* MulAut group) :
    actors →* MulAut (group ⧸ subgroup) :=
  (quotientAutomorphism subgroup).comp action

theorem quotientAction_apply {actors group : Type*} [Group actors] [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (action : actors →* MulAut group)
    (actor : actors) (element : group) :
    quotientAction subgroup action actor (QuotientGroup.mk' subgroup element) =
      QuotientGroup.mk' subgroup (action actor element) :=
  quotientAutomorphism_apply subgroup (action actor) element

theorem quotientAction_quadratic {actors group : Type*} [Group actors] [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (action : actors →* MulAut group)
    (actor : actors) (acts_quadratically : quadratic action actor) :
    quadratic (quotientAction subgroup action) actor := by
  intro element
  obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
  have difference_map : ∀ member : group,
      difference (quotientAction subgroup action actor⁻¹) (QuotientGroup.mk' subgroup member) =
        QuotientGroup.mk' subgroup (difference (action actor⁻¹) member) := by
    intro member
    dsimp only [difference]
    rw [quotientAction_apply, map_mul, map_inv]
    rw [map_inv]
  rw [difference_map, difference_map, acts_quadratically, map_one]

theorem mem_quotientAutomorphism_kernel {group : Type*} [Group group]
    (subgroup : Subgroup group) [subgroup.Characteristic] (automorphism : MulAut group) :
    automorphism ∈ (quotientAutomorphism subgroup).ker ↔
      ∀ element : group, QuotientGroup.mk' subgroup (automorphism element) =
        QuotientGroup.mk' subgroup element := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro equal element
    rw [← quotientAutomorphism_apply, equal]
    rfl
  · intro fixed
    ext element
    obtain ⟨original, rfl⟩ := QuotientGroup.mk'_surjective subgroup element
    exact (quotientAutomorphism_apply subgroup automorphism original).trans (fixed original)

theorem prime_order_frattini_kernel_trivial {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (automorphism : MulAut group)
    (prime_order : orderOf automorphism = prime) (coprime : ¬ prime ∣ Nat.card group)
    (kernel : automorphism ∈ (quotientAutomorphism (frattini group)).ker) :
    automorphism = 1 := by
  let actors := Subgroup.zpowers automorphism
  let action : actors →* MulAut group := actors.subtype
  let induced := quotientAction (frattini group) action
  have actor_prime : IsPGroup prime actors := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, prime_order]
    exact (pow_one prime).symm
  have actors_kernel : actors ≤ (quotientAutomorphism (frattini group)).ker :=
    Subgroup.zpowers_le.mpr kernel
  have induced_fixed : ∀ actor : actors, ∀ element : group ⧸ frattini group,
      induced actor element = element := by
    intro actor element
    have equal := MonoidHom.mem_ker.mp (actors_kernel actor.property)
    change quotientAutomorphism (frattini group) actor.val element = element
    rw [equal]
    rfl
  have fixed_sup : fixedSubgroup action ⊔ frattini group = ⊤ := by
    apply top_unique
    intro element _
    obtain ⟨lift, image_eq, fixed⟩ := exists_fixed_lift_of_coprime prime actor_prime action induced
      (QuotientGroup.mk' (frattini group)) (QuotientGroup.mk'_surjective (frattini group)) coprime
      (fun actor member => (quotientAction_apply (frattini group) action actor member).symm)
      (QuotientGroup.mk' (frattini group) element) (fun actor => induced_fixed actor _)
    apply Subgroup.mem_sup_of_normal_right.mpr
    refine ⟨lift, (mem_fixedSubgroup action lift).mpr fixed, lift⁻¹ * element, ?_, ?_⟩
    · exact QuotientGroup.eq.mp image_eq
    · group
  have fixed_top : fixedSubgroup action = ⊤ := frattini_nongenerating fixed_sup
  ext element
  have element_fixed := (mem_fixedSubgroup action element).mp
    (fixed_top ▸ Subgroup.mem_top element) ⟨automorphism, Subgroup.mem_zpowers automorphism⟩
  exact element_fixed

theorem frattini_automorphism_kernel_isPGroup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_group : IsPGroup prime group) :
    IsPGroup prime (quotientAutomorphism (frattini group)).ker := by
  apply IsPGroup.of_card
  apply Nat.eq_prime_pow_of_unique_prime_dvd (ne_of_gt Nat.card_pos)
  intro divisor divisor_prime divisor_dvd
  by_contra distinct
  have : Fact (Nat.Prime divisor) := ⟨divisor_prime⟩
  obtain ⟨automorphism, prime_order⟩ :=
    exists_prime_orderOf_dvd_card' divisor divisor_dvd
  have ambient_order : orderOf automorphism.val = divisor := by
    rw [Subgroup.orderOf_coe]
    exact prime_order
  obtain ⟨exponent, card_eq⟩ := prime_group.exists_card_eq
  have coprime : ¬ divisor ∣ Nat.card group := by
    rw [card_eq]
    intro divides
    exact distinct (((Fact.out : Nat.Prime prime).dvd_iff_eq divisor_prime.ne_one).mp
      (divisor_prime.dvd_of_dvd_pow divides)).symm
  have trivial := prime_order_frattini_kernel_trivial divisor automorphism.val ambient_order coprime
    automorphism.property
  rw [trivial, orderOf_one] at ambient_order
  exact divisor_prime.ne_one ambient_order.symm

end CFSG.OrderReductions.FrattiniAutomorphisms
