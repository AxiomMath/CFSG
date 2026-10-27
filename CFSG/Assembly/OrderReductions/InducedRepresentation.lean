module

public import CFSG.Assembly.OrderReductions.TIClassFunctionInduction

public section

namespace CFSG.OrderReductions.InducedRepresentation

open CFSG.OrderReductions.TIClassFunctionInduction
open scoped Classical

@[expose] def rightTranslation {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] : Representation field group (group → vector) where
  toFun actor :=
    { toFun := fun function element => function (element * actor)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext function element
    simp
  map_mul' := by
    intro first second
    ext function element
    simp [mul_assoc]

@[expose] def leftTwist {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) :
    Representation field subgroup (group → vector) where
  toFun actor :=
    { toFun := fun function element => representation actor (function (actor.val⁻¹ * element))
      map_add' := by
        intro first second
        funext element
        exact map_add (representation actor) _ _
      map_smul' := by
        intro scalar function
        funext element
        exact map_smul (representation actor) _ _ }
  map_one' := by
    ext function element
    simp
  map_mul' := by
    intro first second
    ext function element
    simp [map_mul, mul_inv_rev, mul_assoc]

theorem translation_twist_commute {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (actor : group) (local_actor : subgroup) :
    rightTranslation (field := field) (vector := vector) actor * leftTwist subgroup representation local_actor =
      leftTwist subgroup representation local_actor * rightTranslation actor := by
  ext function element
  change representation local_actor (function (local_actor.val⁻¹ * (element * actor))) =
    representation local_actor (function (local_actor.val⁻¹ * element * actor))
  congr 2
  exact (mul_assoc _ _ _).symm

theorem translation_preserves_invariants {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (actor : group) :
    (leftTwist subgroup representation).invariants ≤
      (leftTwist subgroup representation).invariants.comap (rightTranslation actor) := by
  intro function invariant
  apply ((leftTwist subgroup representation).mem_invariants _).mpr
  intro local_actor
  have commutes := translation_twist_commute subgroup representation actor local_actor
  have applied := congrArg (fun operator => operator function) commutes
  simpa only [Module.End.mul_apply,
    ((leftTwist subgroup representation).mem_invariants _).mp invariant local_actor] using applied.symm

@[expose] noncomputable def induced {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) :
    Representation field group (leftTwist subgroup representation).invariants :=
  rightTranslation.subrepresentation (leftTwist subgroup representation).invariants
    (translation_preserves_invariants subgroup representation)

@[expose] noncomputable def averaging {field group vector : Type*} [Field field] [Group group] [Fintype group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) : Module.End field (group → vector) :=
  (Nat.card subgroup : field)⁻¹ • ∑ actor : subgroup, leftTwist subgroup representation actor

theorem averaging_invariant {field group vector : Type*} [Field field] [Group group] [Fintype group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (function : group → vector) :
    averaging subgroup representation function ∈ (leftTwist subgroup representation).invariants := by
  apply ((leftTwist subgroup representation).mem_invariants _).mpr
  intro actor
  simp only [averaging, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  simp_rw [← Module.End.mul_apply, ← map_mul]
  change (∑ current : subgroup, leftTwist subgroup representation (actor * current) function) = _
  apply Fintype.sum_equiv (Equiv.mulLeft actor)
  intro current
  rfl

theorem averaging_fixed {field group vector : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] [AddCommGroup vector] [Module field vector]
    (subgroup : Subgroup group) (representation : Representation field subgroup vector)
    (function : group → vector) (invariant : function ∈ (leftTwist subgroup representation).invariants) :
    averaging subgroup representation function = function := by
  have cardinality_ne_zero : (Nat.card subgroup : field) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt Nat.card_pos)
  simp only [averaging, LinearMap.smul_apply, LinearMap.sum_apply,
    ((leftTwist subgroup representation).mem_invariants _).mp invariant,
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul field,
    smul_smul, inv_mul_cancel₀ cardinality_ne_zero, one_smul]

theorem averaging_is_projection {field group vector : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] [AddCommGroup vector] [Module field vector]
    (subgroup : Subgroup group) (representation : Representation field subgroup vector) :
    LinearMap.IsProj (leftTwist subgroup representation).invariants (averaging subgroup representation) :=
  ⟨averaging_invariant subgroup representation, averaging_fixed subgroup representation⟩

theorem trace_pi {field index vector : Type*} [Field field] [Fintype index] [DecidableEq index]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (operator : Module.End field (index → vector)) :
    LinearMap.trace field (index → vector) operator =
      ∑ current : index, LinearMap.trace field vector
        ((LinearMap.proj current).comp (operator.comp (LinearMap.single field (fun _ : index => vector) current))) := by
  have expansion : operator = ∑ current : index,
      (operator.comp (LinearMap.single field (fun _ : index => vector) current)).comp (LinearMap.proj current) := by
    apply LinearMap.ext
    intro function
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
    rw [← map_sum, LinearMap.sum_single_apply]
  conv_lhs => rw [expansion, map_sum]
  apply Finset.sum_congr rfl
  intro current _
  exact LinearMap.trace_comp_comm' (LinearMap.proj current)
    (operator.comp (LinearMap.single field (fun _ : index => vector) current))

theorem trace_restrict_projection {field vector : Type*} [Field field]
    [AddCommGroup vector] [Module field vector] [FiniteDimensional field vector]
    (subspace : Submodule field vector) (operator projector : Module.End field vector)
    (invariant : ∀ element ∈ subspace, operator element ∈ subspace)
    (projection : LinearMap.IsProj subspace projector) :
    LinearMap.trace field subspace (operator.restrict invariant) =
      LinearMap.trace field vector (operator.comp projector) := by
  let retract := projector.codRestrict subspace projection.map_mem
  have restriction_eq : ((operator.restrict invariant).comp retract).comp subspace.subtype =
      operator.restrict invariant := by
    ext element
    exact congrArg operator (projection.map_id element.val element.property)
  have ambient_eq : subspace.subtype.comp ((operator.restrict invariant).comp retract) =
      operator.comp projector := by
    ext element
    rfl
  rw [← restriction_eq, LinearMap.trace_comp_comm', ambient_eq]

theorem translation_average_diagonal {field group vector : Type*} [Field field] [Group group] [Fintype group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (actor conjugator : group) :
    (LinearMap.proj conjugator).comp ((rightTranslation actor).comp (averaging subgroup representation) |>.comp
      (LinearMap.single field (fun _ : group => vector) conjugator)) =
      (Nat.card subgroup : field)⁻¹ •
        (if membership : conjugator * actor * conjugator⁻¹ ∈ subgroup then
          representation ⟨conjugator * actor * conjugator⁻¹, membership⟩ else 0) := by
  have contributing_iff (current : subgroup) :
      current.val⁻¹ * (conjugator * actor) = conjugator ↔
        current.val = conjugator * actor * conjugator⁻¹ := by
    constructor
    · intro equal
      calc
        current.val = current.val * (conjugator * conjugator⁻¹) := by group
        _ = current.val * (current.val⁻¹ * (conjugator * actor)) * conjugator⁻¹ := by
          rw [equal, mul_assoc]
        _ = conjugator * actor * conjugator⁻¹ := by group
    · intro equal
      rw [equal]
      group
  ext value
  change (averaging subgroup representation (Pi.single conjugator value)) (conjugator * actor) = _
  simp only [averaging, LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, Finset.sum_apply]
  change (Nat.card subgroup : field)⁻¹ •
      ∑ current : subgroup, representation current
        ((Pi.single conjugator value : group → vector) (current.val⁻¹ * (conjugator * actor))) = _
  simp_rw [Pi.single_apply, contributing_iff]
  by_cases membership : conjugator * actor * conjugator⁻¹ ∈ subgroup
  · rw [dite_eq_left membership]
    congr 1
    let local_actor : subgroup := ⟨conjugator * actor * conjugator⁻¹, membership⟩
    rw [Finset.sum_eq_single local_actor]
    · simp [local_actor]
    · intro current _ distinct
      have values_distinct : current.val ≠ conjugator * actor * conjugator⁻¹ := by
        intro equal
        exact distinct (Subtype.ext equal)
      simp [values_distinct]
    · simp
  · rw [dite_eq_right membership, LinearMap.zero_apply, smul_zero]
    have zero_sum : (∑ current : subgroup,
        representation current (if current.val = conjugator * actor * conjugator⁻¹ then value else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro current _
      have values_distinct : current.val ≠ conjugator * actor * conjugator⁻¹ := by
        intro equal
        exact membership (equal ▸ current.property)
      simp [values_distinct]
    rw [zero_sum, smul_zero]

theorem induced_character {field group vector : Type*} [Field field] [CharZero field]
    [Group group] [Fintype group] [AddCommGroup vector] [Module field vector]
    [FiniteDimensional field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) :
    (induced subgroup representation).character = inducedFunction subgroup representation.character := by
  funext actor
  change LinearMap.trace field (leftTwist subgroup representation).invariants
      ((rightTranslation actor).restrict (fun element membership =>
        translation_preserves_invariants subgroup representation actor membership)) = _
  rw [trace_restrict_projection _ _ _ _ (averaging_is_projection subgroup representation), trace_pi]
  simp_rw [translation_average_diagonal subgroup representation actor, map_smul]
  change (∑ conjugator : group, (Nat.card subgroup : field)⁻¹ *
    LinearMap.trace field vector (if membership : conjugator * actor * conjugator⁻¹ ∈ subgroup then
      representation ⟨conjugator * actor * conjugator⁻¹, membership⟩ else 0)) = _
  rw [← Finset.mul_sum]
  unfold inducedFunction
  congr 1
  apply Finset.sum_congr rfl
  intro conjugator _
  by_cases membership : conjugator * actor * conjugator⁻¹ ∈ subgroup
  · rw [dite_eq_left membership, zeroExtension, dite_eq_left membership]
    rfl
  · rw [dite_eq_right membership, map_zero, zeroExtension, dite_eq_right membership]

@[expose] noncomputable def linearInduction {field group : Type*} [Field field] [Group group] [Fintype group]
    (subgroup : Subgroup group) : (subgroup → field) →ₗ[field] (group → field) where
  toFun := inducedFunction subgroup
  map_add' := by
    intro first second
    funext element
    have extension_add : ∀ current,
        zeroExtension subgroup (first + second) current =
          zeroExtension subgroup first current + zeroExtension subgroup second current := by
      intro current
      by_cases membership : current ∈ subgroup <;> simp [zeroExtension, membership]
    simp only [inducedFunction, extension_add, Finset.sum_add_distrib, mul_add, Pi.add_apply]
  map_smul' := by
    intro scalar function
    funext element
    have extension_smul : ∀ current,
        zeroExtension subgroup (scalar • function) current = scalar * zeroExtension subgroup function current := by
      intro current
      by_cases membership : current ∈ subgroup <;> simp [zeroExtension, membership]
    simp only [inducedFunction, extension_smul, ← Finset.mul_sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

end CFSG.OrderReductions.InducedRepresentation
