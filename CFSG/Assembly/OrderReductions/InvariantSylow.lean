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
public import CFSG.Assembly.OrderReductions.FixedPairSylow

public section

namespace CFSG.OrderReductions.InvariantSylow

open scoped Pointwise

theorem sylow_card_odd {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_group : Odd (Nat.card group)) :
    Odd (Nat.card (Sylow prime group)) := by
  obtain ⟨sylow⟩ := Sylow.nonempty (p := prime) (G := group)
  exact odd_group.of_dvd_nat (sylow.card_dvd_index.trans
    (sylow : Subgroup group).index_dvd_card)

theorem exists_invariant_sylow_of_odd {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (odd_group : Odd (Nat.card group))
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism) :
    ∃ sylow : Sylow prime group,
      (sylow : Subgroup group).map automorphism.toMonoidHom = sylow := by
  classical
  let := Fintype.ofFinite (Sylow prime group)
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have automorphism_square : automorphism ^ 2 = 1 := by
    ext element
    exact involutive element
  have permutation_square : (MulAction.toPerm automorphism :
      Equiv.Perm (Sylow prime group)) ^ (2 ^ 1) = 1 := by
    change (MulAction.toPermHom (MulAut group) (Sylow prime group) automorphism) ^ (2 ^ 1) = 1
    rw [← map_pow, show 2 ^ 1 = 2 from rfl, automorphism_square, map_one]
  have odd_sylows := sylow_card_odd prime odd_group
  have not_divides : ¬ 2 ∣ Fintype.card (Sylow prime group) := by
    rw [← Nat.card_eq_fintype_card]
    exact odd_sylows.not_two_dvd_nat
  obtain ⟨sylow, fixed⟩ := Equiv.Perm.exists_fixed_point_of_prime not_divides permutation_square
  have fixed_sylow : (automorphism • sylow : Sylow prime group) = sylow := fixed
  have fixed_subgroup := congrArg (fun current : Sylow prime group =>
    (current : Subgroup group)) fixed_sylow
  rw [Sylow.pointwise_smul_def] at fixed_subgroup
  exact ⟨sylow, fixed_subgroup⟩

@[expose] def restrictedAutomorphism {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) : MulAut subgroup :=
  (automorphism.subgroupMap subgroup).trans (MulEquiv.subgroupCongr invariant)

theorem restrictedAutomorphism_apply {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) (element : subgroup) :
    (restrictedAutomorphism automorphism subgroup invariant element).val =
      automorphism element.val := rfl

theorem restrictedAutomorphism_involutive {group : Type*} [Group group]
    (automorphism : MulAut group) (involutive : Function.Involutive automorphism)
    (subgroup : Subgroup group) (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    Function.Involutive (restrictedAutomorphism automorphism subgroup invariant) := by
  intro element
  apply Subtype.ext
  exact involutive element.val

theorem normalizer_invariant {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup : Subgroup group)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    (Subgroup.normalizer (subgroup : Set group)).map automorphism.toMonoidHom =
      Subgroup.normalizer (subgroup : Set group) := by
  rw [Subgroup.map_normalizer_eq_of_bijective subgroup automorphism.bijective, invariant]

theorem map_subtype_invariant {group : Type*} [Group group]
    (automorphism : MulAut group) (ambient : Subgroup group)
    (ambient_invariant : ambient.map automorphism.toMonoidHom = ambient)
    (subgroup : Subgroup ambient)
    (invariant : subgroup.map
      (restrictedAutomorphism automorphism ambient ambient_invariant).toMonoidHom = subgroup) :
    (subgroup.map ambient.subtype).map automorphism.toMonoidHom =
      subgroup.map ambient.subtype := by
  have intertwines : automorphism.toMonoidHom.comp ambient.subtype =
      ambient.subtype.comp
        (restrictedAutomorphism automorphism ambient ambient_invariant).toMonoidHom := by
    ext element
    rfl
  rw [Subgroup.map_map, intertwines, ← Subgroup.map_map, invariant]

theorem exists_invariant_sylow_containing_of_odd {group : Type*}
    [Group group] [Finite group] (prime : ℕ) [Fact (Nat.Prime prime)]
    (odd_group : Odd (Nat.card group)) (automorphism : MulAut group)
    (involutive : Function.Involutive automorphism)
    (subgroup : Subgroup group) (prime_group : IsPGroup prime subgroup)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    ∃ sylow : Sylow prime group, subgroup ≤ (sylow : Subgroup group) ∧
      (sylow : Subgroup group).map automorphism.toMonoidHom = sylow := by
  obtain ⟨maximal_group, contains, maximal⟩ := Finite.exists_le_maximal
    (p := fun current : Subgroup group => IsPGroup prime current ∧
      current.map automorphism.toMonoidHom = current) ⟨prime_group, invariant⟩
  have maximal_prime := maximal.prop.1
  have maximal_invariant := maximal.prop.2
  let normalizer := Subgroup.normalizer (maximal_group : Set group)
  have normalizer_invariant := normalizer_invariant automorphism maximal_group maximal_invariant
  let restricted := restrictedAutomorphism automorphism normalizer normalizer_invariant
  have restricted_involutive : Function.Involutive restricted :=
    restrictedAutomorphism_involutive automorphism involutive normalizer normalizer_invariant
  have normalizer_odd : Odd (Nat.card normalizer) :=
    odd_group.of_dvd_nat normalizer.card_subgroup_dvd_card
  obtain ⟨internal, internal_invariant⟩ := exists_invariant_sylow_of_odd prime normalizer_odd
    restricted restricted_involutive
  have internal_contains : maximal_group.subgroupOf normalizer ≤
      (internal : Subgroup normalizer) := by
    have restricted_prime : IsPGroup prime (maximal_group.subgroupOf normalizer) :=
      maximal_prime.of_equiv
        (Subgroup.subgroupOfEquivOfLe maximal_group.le_normalizer).symm
    exact restricted_prime.le_sylow_of_normal internal
  let image := (internal : Subgroup normalizer).map normalizer.subtype
  have image_prime : IsPGroup prime image := internal.isPGroup'.map normalizer.subtype
  have image_invariant : image.map automorphism.toMonoidHom = image :=
    map_subtype_invariant automorphism normalizer normalizer_invariant internal internal_invariant
  have maximal_le : maximal_group ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le maximal_group.le_normalizer]
    exact Subgroup.map_mono internal_contains
  have equal_image : maximal_group = image :=
    maximal.eq_of_le ⟨image_prime, image_invariant⟩ maximal_le
  have normalizer_le : Subgroup.normalizer (image : Set group) ≤ normalizer := by
    rw [← equal_image]
  obtain ⟨sylow, sylow_image⟩ := CFSG.OrderReductions.FixedPairSylow.sylow_extension_of_normalizer_le
    prime normalizer internal normalizer_le
  refine ⟨sylow, ?_, ?_⟩
  · rw [sylow_image]
    exact contains.trans maximal_le
  · rw [sylow_image]
    exact image_invariant

theorem exists_invariant_sylow_of_coprime {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)]
    [Fact (Nat.Prime sylow_prime)] (prime_actor : IsPGroup acting_prime actor)
    (coprime : ¬ acting_prime ∣ Nat.card group) (homomorphism : actor →* MulAut group) :
    ∃ sylow : Sylow sylow_prime group, ∀ element : actor,
      (sylow : Subgroup group).map (homomorphism element).toMonoidHom = sylow := by
  let := MulDistribMulAction.compHom group homomorphism
  obtain ⟨sample⟩ := Sylow.nonempty (p := sylow_prime) (G := group)
  have not_divides : ¬ acting_prime ∣ Nat.card (Sylow sylow_prime group) := by
    intro divides
    exact coprime (divides.trans (sample.card_dvd_index.trans
      (sample : Subgroup group).index_dvd_card))
  obtain ⟨sylow, fixed⟩ := prime_actor.nonempty_fixed_point_of_prime_not_dvd_card
    (Sylow sylow_prime group) not_divides
  refine ⟨sylow, ?_⟩
  intro element
  have fixed_subgroup := congrArg (fun current : Sylow sylow_prime group =>
    (current : Subgroup group)) (MulAction.mem_fixedPoints.mp fixed element)
  rw [Sylow.pointwise_smul_def] at fixed_subgroup
  exact fixed_subgroup

@[expose] def restrictedHomomorphism {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) (subgroup : Subgroup group)
    (invariant : ∀ element : actor,
      subgroup.map (homomorphism element).toMonoidHom = subgroup) : actor →* MulAut subgroup where
  toFun element := restrictedAutomorphism (homomorphism element) subgroup (invariant element)
  map_one' := by
    ext element
    change homomorphism 1 element.val = element.val
    rw [map_one]
    rfl
  map_mul' first second := by
    ext element
    change homomorphism (first * second) element.val =
      homomorphism first (homomorphism second element.val)
    rw [map_mul]
    rfl

theorem exists_invariant_sylow_containing_of_coprime {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)]
    [Fact (Nat.Prime sylow_prime)] (prime_actor : IsPGroup acting_prime actor)
    (coprime : ¬ acting_prime ∣ Nat.card group) (homomorphism : actor →* MulAut group)
    (subgroup : Subgroup group) (prime_group : IsPGroup sylow_prime subgroup)
    (invariant : ∀ element : actor,
      subgroup.map (homomorphism element).toMonoidHom = subgroup) :
    ∃ sylow : Sylow sylow_prime group, subgroup ≤ (sylow : Subgroup group) ∧
      ∀ element : actor,
        (sylow : Subgroup group).map (homomorphism element).toMonoidHom = sylow := by
  obtain ⟨maximal_group, contains, maximal⟩ := Finite.exists_le_maximal
    (p := fun current : Subgroup group => IsPGroup sylow_prime current ∧
      ∀ element : actor, current.map (homomorphism element).toMonoidHom = current)
    ⟨prime_group, invariant⟩
  have maximal_prime := maximal.prop.1
  have maximal_invariant := maximal.prop.2
  let normalizer := Subgroup.normalizer (maximal_group : Set group)
  have normalizer_invariant : ∀ element : actor,
      normalizer.map (homomorphism element).toMonoidHom = normalizer := fun element =>
    normalizer_invariant (homomorphism element) maximal_group (maximal_invariant element)
  let restricted := restrictedHomomorphism homomorphism normalizer normalizer_invariant
  have normalizer_coprime : ¬ acting_prime ∣ Nat.card normalizer := fun divides =>
    coprime (divides.trans normalizer.card_subgroup_dvd_card)
  obtain ⟨internal, internal_invariant⟩ := exists_invariant_sylow_of_coprime
    acting_prime sylow_prime prime_actor normalizer_coprime restricted
  have internal_contains : maximal_group.subgroupOf normalizer ≤
      (internal : Subgroup normalizer) := by
    have restricted_prime : IsPGroup sylow_prime (maximal_group.subgroupOf normalizer) :=
      maximal_prime.of_equiv
        (Subgroup.subgroupOfEquivOfLe maximal_group.le_normalizer).symm
    exact restricted_prime.le_sylow_of_normal internal
  let image := (internal : Subgroup normalizer).map normalizer.subtype
  have image_prime : IsPGroup sylow_prime image := internal.isPGroup'.map normalizer.subtype
  have image_invariant : ∀ element : actor,
      image.map (homomorphism element).toMonoidHom = image := fun element =>
    map_subtype_invariant (homomorphism element) normalizer (normalizer_invariant element)
      internal (internal_invariant element)
  have maximal_le : maximal_group ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le maximal_group.le_normalizer]
    exact Subgroup.map_mono internal_contains
  have equal_image : maximal_group = image :=
    maximal.eq_of_le ⟨image_prime, image_invariant⟩ maximal_le
  have normalizer_le : Subgroup.normalizer (image : Set group) ≤ normalizer := by
    rw [← equal_image]
  obtain ⟨sylow, sylow_image⟩ := CFSG.OrderReductions.FixedPairSylow.sylow_extension_of_normalizer_le
    sylow_prime normalizer internal normalizer_le
  refine ⟨sylow, ?_, ?_⟩
  · rw [sylow_image]
    exact contains.trans maximal_le
  · intro element
    rw [sylow_image]
    exact image_invariant element

theorem restricted_invariant_iff {group : Type*} [Group group]
    (automorphism : MulAut group) (ambient : Subgroup group)
    (ambient_invariant : ambient.map automorphism.toMonoidHom = ambient)
    (subgroup : Subgroup ambient) :
    subgroup.map (restrictedAutomorphism automorphism ambient ambient_invariant).toMonoidHom =
        subgroup ↔
      (subgroup.map ambient.subtype).map automorphism.toMonoidHom =
        subgroup.map ambient.subtype := by
  constructor
  · exact map_subtype_invariant automorphism ambient ambient_invariant subgroup
  · intro invariant
    apply Subgroup.map_injective (f := ambient.subtype) Subtype.val_injective
    have intertwines : ambient.subtype.comp
        (restrictedAutomorphism automorphism ambient ambient_invariant).toMonoidHom =
      automorphism.toMonoidHom.comp ambient.subtype := by
      ext element
      rfl
    rw [Subgroup.map_map, intertwines, ← Subgroup.map_map]
    exact invariant

theorem subgroupOf_invariant {group : Type*} [Group group]
    (automorphism : MulAut group) (subgroup ambient : Subgroup group)
    (contains : subgroup ≤ ambient)
    (ambient_invariant : ambient.map automorphism.toMonoidHom = ambient)
    (invariant : subgroup.map automorphism.toMonoidHom = subgroup) :
    (subgroup.subgroupOf ambient).map
      (restrictedAutomorphism automorphism ambient ambient_invariant).toMonoidHom =
        subgroup.subgroupOf ambient := by
  apply (restricted_invariant_iff automorphism ambient ambient_invariant
    (subgroup.subgroupOf ambient)).mpr
  rw [Subgroup.map_subgroupOf_eq_of_le contains]
  exact invariant

end CFSG.OrderReductions.InvariantSylow
