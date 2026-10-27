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
public import CFSG.Assembly.OrderReductions.FixedConjugator

public section

namespace CFSG.OrderReductions.CoprimeFixedSubgroup

@[expose] def fixedSubgroup {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) : Subgroup group :=
  ⨅ acting : actor, (homomorphism acting).toMonoidHom.eqLocus (MonoidHom.id group)

theorem mem_fixedSubgroup {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) (element : group) :
    element ∈ fixedSubgroup homomorphism ↔
      ∀ acting : actor, homomorphism acting element = element := by
  rw [fixedSubgroup, Subgroup.mem_iInf]
  rfl

theorem map_eq_self_of_le_fixed {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) (subgroup : Subgroup group)
    (fixed : subgroup ≤ fixedSubgroup homomorphism) (acting : actor) :
    subgroup.map (homomorphism acting).toMonoidHom = subgroup := by
  ext element
  constructor
  · intro mem_image
    obtain ⟨original, mem_original, equal_image⟩ := Subgroup.mem_map.mp mem_image
    have original_fixed := (mem_fixedSubgroup homomorphism original).mp
      (fixed mem_original) acting
    have equal_original : original = element := original_fixed.symm.trans equal_image
    exact equal_original ▸ mem_original
  · intro mem_subgroup
    exact Subgroup.mem_map.mpr ⟨element, mem_subgroup,
      (mem_fixedSubgroup homomorphism element).mp (fixed mem_subgroup) acting⟩

theorem fixed_element_normalizes_fixed {actor group : Type*} [Group actor] [Group group]
    (homomorphism : actor →* MulAut group) (element : group)
    (fixed : ∀ acting : actor, homomorphism acting element = element) :
    (fixedSubgroup homomorphism).map (MulAut.conj element).toMonoidHom =
      fixedSubgroup homomorphism := by
  have mem_fixed := (mem_fixedSubgroup homomorphism element).mpr fixed
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    ((fixedSubgroup homomorphism).le_normalizer mem_fixed)

theorem sylow_fixed_intersection {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)]
    [Fact (Nat.Prime sylow_prime)] (prime_actor : IsPGroup acting_prime actor)
    (coprime : ¬ acting_prime ∣ Nat.card group) (homomorphism : actor →* MulAut group)
    (sylow : Sylow sylow_prime group)
    (invariant : ∀ element : actor,
      (sylow : Subgroup group).map (homomorphism element).toMonoidHom = sylow) :
    ∃ fixed_sylow : Sylow sylow_prime (fixedSubgroup homomorphism),
      (fixed_sylow : Subgroup (fixedSubgroup homomorphism)).map
        (fixedSubgroup homomorphism).subtype =
          (sylow : Subgroup group) ⊓ fixedSubgroup homomorphism := by
  let fixed := fixedSubgroup homomorphism
  let intersection := (sylow : Subgroup group) ⊓ fixed
  have intersection_prime : IsPGroup sylow_prime intersection :=
    sylow.isPGroup'.to_le inf_le_left
  have internal_prime : IsPGroup sylow_prime (intersection.subgroupOf fixed) :=
    intersection_prime.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨fixed_sylow, contains⟩ := internal_prime.exists_le_sylow
  let image := (fixed_sylow : Subgroup fixed).map fixed.subtype
  have image_prime : IsPGroup sylow_prime image := fixed_sylow.isPGroup'.map fixed.subtype
  have image_le : image ≤ fixed := by
    intro element mem_image
    obtain ⟨original, _, equal_image⟩ := Subgroup.mem_map.mp mem_image
    exact equal_image ▸ original.property
  have image_invariant : ∀ acting : actor,
      image.map (homomorphism acting).toMonoidHom = image :=
    map_eq_self_of_le_fixed homomorphism image image_le
  obtain ⟨ambient_sylow, image_contains, ambient_invariant⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_containing_of_coprime
      acting_prime sylow_prime prime_actor coprime homomorphism image image_prime image_invariant
  obtain ⟨conjugator, conjugates, conjugator_fixed⟩ :=
    CFSG.OrderReductions.FixedConjugator.invariant_sylows_conjugate_of_coprime
      acting_prime sylow_prime prime_actor coprime homomorphism ambient_sylow sylow
        ambient_invariant invariant
  have conjugate_le_sylow : image.map (MulAut.conj conjugator).toMonoidHom ≤
      (sylow : Subgroup group) := by
    rw [← conjugates]
    exact Subgroup.map_mono image_contains
  have conjugate_le_fixed : image.map (MulAut.conj conjugator).toMonoidHom ≤ fixed := by
    have mapped_le := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) image_le
    rw [fixed_element_normalizes_fixed homomorphism conjugator conjugator_fixed] at mapped_le
    exact mapped_le
  have conjugate_le : image.map (MulAut.conj conjugator).toMonoidHom ≤ intersection :=
    le_inf conjugate_le_sylow conjugate_le_fixed
  have card_le := Nat.le_of_dvd (Nat.card_pos (α := intersection))
    (Subgroup.card_dvd_of_le conjugate_le)
  rw [Subgroup.card_map_of_injective (MulAut.conj conjugator).injective] at card_le
  have intersection_le : intersection ≤ image := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (show intersection ≤ fixed from inf_le_right)]
    exact Subgroup.map_mono contains
  have equal_image : intersection = image :=
    Subgroup.eq_of_le_of_card_ge intersection_le card_le
  exact ⟨fixed_sylow, equal_image.symm⟩

theorem sylow_fixed_intersection_card {actor group : Type*}
    [Group actor] [Group group] [Finite group]
    (acting_prime sylow_prime : ℕ) [Fact (Nat.Prime acting_prime)]
    [Fact (Nat.Prime sylow_prime)] (prime_actor : IsPGroup acting_prime actor)
    (coprime : ¬ acting_prime ∣ Nat.card group) (homomorphism : actor →* MulAut group)
    (sylow : Sylow sylow_prime group)
    (invariant : ∀ element : actor,
      (sylow : Subgroup group).map (homomorphism element).toMonoidHom = sylow) :
    Nat.card ↥((sylow : Subgroup group) ⊓ fixedSubgroup homomorphism) =
      sylow_prime ^ (Nat.card (fixedSubgroup homomorphism)).factorization sylow_prime := by
  obtain ⟨fixed_sylow, equal_intersection⟩ := sylow_fixed_intersection
    acting_prime sylow_prime prime_actor coprime homomorphism sylow invariant
  rw [← equal_intersection, Subgroup.card_map_of_injective Subtype.val_injective,
    fixed_sylow.card_eq_multiplicity]

end CFSG.OrderReductions.CoprimeFixedSubgroup
