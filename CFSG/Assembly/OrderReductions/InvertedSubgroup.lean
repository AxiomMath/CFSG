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
public import CFSG.Assembly.OrderReductions.InvariantSylow
public import CFSG.Assembly.OrderReductions.PrimeInvolutionGeneration
public import CFSG.Assembly.OrderReductions.PrimeInvolutionSylow

public section

namespace CFSG.OrderReductions.InvertedSubgroup

@[expose] def invertedSubgroup {group : Type*} [Group group] (automorphism : MulAut group) : Subgroup group :=
  Subgroup.closure {element : group | automorphism element = element⁻¹}

theorem commutator_mem {group : Type*} [Group group] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) (element : group) :
    element * (automorphism element)⁻¹ ∈ invertedSubgroup automorphism := by
  apply Subgroup.subset_closure
  change automorphism (element * (automorphism element)⁻¹) = (element * (automorphism element)⁻¹)⁻¹
  rw [map_mul, map_inv, involutive, mul_inv_rev, inv_inv]

theorem normal {group : Type*} [Group group] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) : (invertedSubgroup automorphism).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  intro conjugator _ element inverted
  have twisted_mem : conjugator * element * (automorphism conjugator)⁻¹ ∈
      invertedSubgroup automorphism := by
    apply Subgroup.subset_closure
    exact CFSG.OrderReductions.PrimeInvolutionGeneration.twisted_actor_inverted
      automorphism involutive conjugator element inverted
  have inverse_commutator_mem := (invertedSubgroup automorphism).inv_mem
    (commutator_mem automorphism involutive conjugator)
  have product_mem := (invertedSubgroup automorphism).mul_mem twisted_mem inverse_commutator_mem
  have product_eq : conjugator * element * (automorphism conjugator)⁻¹ *
      (conjugator * (automorphism conjugator)⁻¹)⁻¹ = conjugator * element * conjugator⁻¹ := by group
  rw [product_eq] at product_mem
  exact product_mem

theorem invariant {group : Type*} [Group group] (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism) :
    (invertedSubgroup automorphism).map automorphism.toMonoidHom = invertedSubgroup automorphism := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    intro element inverted
    change automorphism element ∈ invertedSubgroup automorphism
    rw [inverted]
    exact (invertedSubgroup automorphism).inv_mem (Subgroup.subset_closure inverted)
  · intro element element_mem
    have image_le : (invertedSubgroup automorphism).map automorphism.toMonoidHom ≤
        invertedSubgroup automorphism := by
      apply Subgroup.map_le_iff_le_comap.mpr
      apply (Subgroup.closure_le _).mpr
      intro original inverted
      change automorphism original ∈ invertedSubgroup automorphism
      rw [inverted]
      exact (invertedSubgroup automorphism).inv_mem (Subgroup.subset_closure inverted)
    have image_mem : automorphism element ∈ invertedSubgroup automorphism :=
      image_le (Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨automorphism element, image_mem, involutive element⟩

theorem generated_by_internal_inverted {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism) :
    let subgroup := invertedSubgroup automorphism
    let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism subgroup
      (invariant automorphism involutive)
    Subgroup.closure {element : subgroup | restricted element = element⁻¹} = ⊤ := by
  let subgroup := invertedSubgroup automorphism
  let restricted := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism automorphism subgroup
    (invariant automorphism involutive)
  let internal := Subgroup.closure {element : subgroup | restricted element = element⁻¹}
  have image_eq : internal.map subgroup.subtype = subgroup := by
    apply le_antisymm (Subgroup.map_subtype_le internal)
    apply (Subgroup.closure_le _).mpr
    intro element inverted
    let original : subgroup := ⟨element, Subgroup.subset_closure inverted⟩
    have original_inverted : restricted original = original⁻¹ := Subtype.ext inverted
    exact Subgroup.mem_map.mpr ⟨original, Subgroup.subset_closure original_inverted, rfl⟩
  apply Subgroup.map_injective (f := subgroup.subtype) Subtype.val_injective
  rw [image_eq, ← MonoidHom.range_eq_map, Subgroup.subtype_range]

theorem fixed_by_generators_iff {actor group : Type*} [Group actor] [Group group]
    (action : actor →* MulAut group) (automorphism : MulAut actor) (element : group) :
    (∀ acting : actor, automorphism acting = acting⁻¹ → action acting element = element) ↔
      ∀ acting : invertedSubgroup automorphism, action acting.val element = element := by
  constructor
  · intro fixed acting
    let closed : Subgroup actor :=
      { carrier := {acting | action acting element = element}
        one_mem' := by
          change action 1 element = element
          rw [map_one]
          rfl
        mul_mem' := fun {first second} first_fixed second_fixed => by
          change action (first * second) element = element
          change action first element = element at first_fixed
          change action second element = element at second_fixed
          rw [CFSG.OrderReductions.PrimeInvolutionGeneration.action_mul_apply, second_fixed, first_fixed]
        inv_mem' := fun {original} original_fixed => by
          change action original⁻¹ element = element
          change action original element = element at original_fixed
          apply (action original).injective
          change (action original * action original⁻¹ : MulAut group) element = action original element
          rw [← map_mul, mul_inv_cancel, map_one, original_fixed]
          rfl }
    have contains : invertedSubgroup automorphism ≤ closed := (Subgroup.closure_le closed).mpr fixed
    exact contains acting.property
  · intro fixed acting inverted
    exact fixed ⟨acting, Subgroup.subset_closure inverted⟩

theorem odd_prime_involution_generation {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_actor : IsPGroup prime actor)
    (coprime : ¬ prime ∣ Nat.card group) (odd_group : Odd (Nat.card group))
    (action : actor →* MulAut group) (actor_automorphism : MulAut actor)
    (actor_involutive : Function.Involutive actor_automorphism)
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (compatible : ∀ acting : actor, ∀ element : group,
      automorphism (action acting element) = action (actor_automorphism acting) (automorphism element))
    (subgroup : Subgroup group)
    (inverted_fixed : ∀ element : group,
      (∀ acting : actor, actor_automorphism acting = acting⁻¹ → action acting element = element) →
        element ∈ subgroup)
    (twisted_fixed : ∀ acting : actor, actor_automorphism acting = acting⁻¹ → ∀ element : group,
      (action acting * automorphism : MulAut group) element = element → element ∈ subgroup) :
    subgroup = ⊤ := by
  let inverted := invertedSubgroup actor_automorphism
  let restricted_actor := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism
    actor_automorphism inverted (invariant actor_automorphism actor_involutive)
  let restricted_action : inverted →* MulAut group := action.comp inverted.subtype
  have restricted_involutive := CFSG.OrderReductions.InvariantSylow.restrictedAutomorphism_involutive
    actor_automorphism actor_involutive inverted (invariant actor_automorphism actor_involutive)
  have restricted_generated := generated_by_internal_inverted actor_automorphism actor_involutive
  apply CFSG.OrderReductions.PrimeInvolutionSylow.odd_fixed_generation prime (prime_actor.to_subgroup inverted)
    coprime odd_group restricted_action restricted_actor restricted_involutive restricted_generated
    automorphism involutive (fun acting element => compatible acting.val element) subgroup
  · intro element fixed
    exact inverted_fixed element ((fixed_by_generators_iff action actor_automorphism element).mpr fixed)
  · intro acting acting_inverted element fixed
    exact twisted_fixed acting.val (congrArg Subtype.val acting_inverted) element fixed

end CFSG.OrderReductions.InvertedSubgroup
