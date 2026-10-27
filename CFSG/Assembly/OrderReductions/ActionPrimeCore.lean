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
public import CFSG.Assembly.OrderReductions.PrimeComplementCore
public import CFSG.Assembly.OrderReductions.PrimeCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.ClassTwoCubic
public import CFSG.Assembly.OrderReductions.CubicConjugation

public section

namespace CFSG.OrderReductions.ActionPrimeCore

open CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.ClassTwoCubic CFSG.OrderReductions.CubicConjugation

@[expose] def actionCore {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) : Subgroup actors :=
  (primeCore prime (actors ⧸ action.ker)).comap (QuotientGroup.mk' action.ker)

@[expose] def quadratic {actors target : Type*} [Group actors] [Group target]
    (action : actors →* MulAut target) (actor : actors) : Prop :=
  ∀ element : target, difference (action actor⁻¹) (difference (action actor⁻¹) element) = 1

@[expose] def primeStable {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) : Prop :=
  ∀ actor : actors, quadratic action actor → actor ∈ actionCore prime action

instance actionCore_normal {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) : (actionCore prime action).Normal :=
  inferInstanceAs ((primeCore prime (actors ⧸ action.ker)).comap (QuotientGroup.mk' action.ker)).Normal

theorem kernel_le_actionCore {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) : action.ker ≤ actionCore prime action := by
  intro actor actor_mem
  change QuotientGroup.mk' action.ker actor ∈ primeCore prime (actors ⧸ action.ker)
  have projection_mem : actor ∈ (QuotientGroup.mk' action.ker).ker := by
    rwa [QuotientGroup.ker_mk']
  rw [MonoidHom.mem_ker.mp projection_mem]
  exact Subgroup.one_mem _

theorem primeCore_le_actionCore {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) : primeCore prime actors ≤ actionCore prime action :=
  Subgroup.map_le_iff_le_comap.mp
    (map_core_le_of_surjective prime (QuotientGroup.mk' action.ker) (QuotientGroup.mk'_surjective action.ker))

theorem actionCore_eq_primeCore_of_prime_kernel {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) (prime_kernel : IsPGroup prime action.ker) :
    actionCore prime action = primeCore prime actors := by
  have projection_kernel : IsPGroup prime (QuotientGroup.mk' action.ker).ker := by
    rw [QuotientGroup.ker_mk']
    exact prime_kernel
  have prime_preimage : IsPGroup prime (actionCore prime action) :=
    (primeCore_isPGroup prime (actors ⧸ action.ker)).comap_of_ker_isPGroup
      (QuotientGroup.mk' action.ker) projection_kernel
  exact le_antisymm (normal_le_primeCore prime _ prime_preimage) (primeCore_le_actionCore prime action)

@[expose] def conjugationAction {group : Type*} [Group group] (normal : Subgroup group) [normal.Normal] :
    group →* MulAut normal where
  toFun actor := rightConjugation normal actor⁻¹
  map_one' := by
    ext element
    change (1 : group)⁻¹⁻¹ * element.val * 1⁻¹ = element.val
    simp only [inv_one, one_mul, mul_one]
  map_mul' first second := by
    ext element
    change ((first * second)⁻¹)⁻¹ * element.val * (first * second)⁻¹ =
      first⁻¹⁻¹ * (second⁻¹⁻¹ * element.val * second⁻¹) * first⁻¹
    group

theorem conjugationAction_apply {group : Type*} [Group group]
    (normal : Subgroup group) [normal.Normal] (actor : group) (element : normal) :
    (conjugationAction normal actor element).val = actor * element.val * actor⁻¹ := by
  change actor⁻¹⁻¹ * element.val * actor⁻¹ = actor * element.val * actor⁻¹
  rw [inv_inv]

theorem conjugationAction_kernel {group : Type*} [Group group]
    (normal : Subgroup group) [normal.Normal] :
    (conjugationAction normal).ker = Subgroup.centralizer (normal : Set group) := by
  ext actor
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro equal element element_mem
    have fixed := congrArg (fun automorphism : MulAut normal => (automorphism ⟨element, element_mem⟩).val) equal
    rw [conjugationAction_apply] at fixed
    change actor * element * actor⁻¹ = element at fixed
    have multiplied := congrArg (fun value : group => value * actor) fixed
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using multiplied.symm
  · intro commutes
    ext element
    rw [conjugationAction_apply]
    change actor * element.val * actor⁻¹ = element.val
    rw [← commutes element.val element.property, mul_assoc, mul_inv_cancel, mul_one]

theorem quadratic_conjugation_iff {group : Type*} [Group group]
    (normal : Subgroup group) [normal.Normal] (actor : group) :
    quadratic (conjugationAction normal) actor ↔
      ∀ element : normal, inverseFirstCommutator (inverseFirstCommutator element.val actor) actor = 1 := by
  constructor
  · intro acts_quadratically element
    have equal := congrArg (fun value : normal => value.val) (acts_quadratically element)
    change (difference (rightConjugation normal actor⁻¹⁻¹)
      (difference (rightConjugation normal actor⁻¹⁻¹) element)).val = 1 at equal
    simpa only [inv_inv, difference_val] using equal
  · intro cubic element
    apply Subtype.ext
    change (difference (rightConjugation normal actor⁻¹⁻¹)
      (difference (rightConjugation normal actor⁻¹⁻¹) element)).val = 1
    simpa only [inv_inv, difference_val] using cubic element

theorem actionCore_primeCore_eq_of_self_centralizing {group : Type*} [Group group]
    (prime : ℕ) (self_centralizing : Subgroup.centralizer (primeCore prime group : Set group) ≤ primeCore prime group) :
    actionCore prime (conjugationAction (primeCore prime group)) = primeCore prime group := by
  apply actionCore_eq_primeCore_of_prime_kernel
  rw [conjugationAction_kernel]
  exact (primeCore_isPGroup prime group).to_le self_centralizing

theorem actionCore_quotient_isPGroup {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) :
    IsPGroup prime ((actionCore prime action) ⧸ action.ker.subgroupOf (actionCore prime action)) := by
  let projection := QuotientGroup.mk' action.ker
  let core := primeCore prime (actors ⧸ action.ker)
  let restricted : actionCore prime action →* core :=
    (projection.comp (actionCore prime action).subtype).codRestrict core (fun element => element.property)
  have surjective : Function.Surjective restricted := by
    intro element
    obtain ⟨original, equal⟩ := QuotientGroup.mk'_surjective action.ker element.val
    refine ⟨⟨original, ?_⟩, ?_⟩
    · change projection original ∈ core
      rw [equal]
      exact element.property
    · exact Subtype.ext equal
  have kernel_eq : restricted.ker = action.ker.subgroupOf (actionCore prime action) := by
    ext element
    rw [MonoidHom.mem_ker]
    change (⟨projection element.val, element.property⟩ : core) = 1 ↔ element.val ∈ action.ker
    rw [Subtype.ext_iff]
    change projection element.val = 1 ↔ element.val ∈ action.ker
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  have prime_quotient : IsPGroup prime ((actionCore prime action) ⧸ restricted.ker) :=
    (primeCore_isPGroup prime (actors ⧸ action.ker)).of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective restricted surjective).symm
  exact prime_quotient.of_equiv
    (QuotientGroup.congr restricted.ker (action.ker.subgroupOf (actionCore prime action))
      (MulEquiv.refl _) (by
        change restricted.ker.map (MonoidHom.id _) = _
        rw [Subgroup.map_id]
        exact kernel_eq))

end CFSG.OrderReductions.ActionPrimeCore
