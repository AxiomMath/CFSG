module

public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms

public section

namespace CFSG.OrderReductions.ActionImageCore

open CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore CFSG.OrderReductions.FrattiniAutomorphisms

theorem actionCore_mem_iff_range {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) (actor : actors) :
    actor ∈ actionCore prime action ↔
      action.rangeRestrict actor ∈ primeCore prime action.range := by
  let equivalence := QuotientGroup.quotientKerEquivRange action
  have core_eq := map_core_eq_of_equiv prime equivalence
  have image_eq : equivalence (QuotientGroup.mk' action.ker actor) = action.rangeRestrict actor := rfl
  constructor
  · intro membership
    rw [← core_eq, ← image_eq]
    exact Subgroup.mem_map.mpr ⟨QuotientGroup.mk' action.ker actor, membership, rfl⟩
  · intro membership
    rw [← core_eq] at membership
    obtain ⟨original, original_mem, original_eq⟩ := Subgroup.mem_map.mp membership
    have equal := equivalence.injective (original_eq.trans image_eq.symm)
    change QuotientGroup.mk' action.ker actor ∈ primeCore prime (actors ⧸ action.ker)
    exact equal ▸ original_mem

theorem actionCore_eq_range_comap {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target) :
    actionCore prime action = (primeCore prime action.range).comap action.rangeRestrict := by
  ext actor
  exact actionCore_mem_iff_range prime action actor

theorem quadratic_range_action {actors target : Type*} [Group actors] [Group target]
    (action : actors →* MulAut target) (actor : actors) :
    quadratic action.range.subtype (action.rangeRestrict actor) ↔ quadratic action actor := by
  simp only [quadratic, map_inv]
  rfl

theorem primeStable_of_range_action {actors target : Type*} [Group actors] [Group target]
    (prime : ℕ) (action : actors →* MulAut target)
    (stable_image : primeStable prime action.range.subtype) : primeStable prime action := by
  intro actor quadratic_actor
  apply (actionCore_mem_iff_range prime action actor).mpr
  have kernel_prime : IsPGroup prime action.range.subtype.ker :=
    IsPGroup.ker_isPGroup_of_injective Subtype.val_injective
  rw [← actionCore_eq_primeCore_of_prime_kernel prime action.range.subtype kernel_prime]
  exact stable_image _ ((quadratic_range_action action actor).mpr quadratic_actor)

theorem primeStable_of_frattini_quotient_faithful {actors target : Type*} [Group actors]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_target : IsPGroup prime target) (action : actors →* MulAut target)
    (faithful : Function.Injective action)
    (stable_quotient : primeStable prime (quotientAction (frattini target) action)) :
    primeStable prime action := by
  have prime_kernel : IsPGroup prime (quotientAction (frattini target) action).ker := by
    change IsPGroup prime (((quotientAutomorphism (frattini target)).comp action).ker)
    rw [← MonoidHom.comap_ker]
    exact (frattini_automorphism_kernel_isPGroup prime prime_target).comap_of_injective action faithful
  intro actor quadratic_actor
  have quotient_mem := stable_quotient actor
    (quotientAction_quadratic (frattini target) action actor quadratic_actor)
  rw [actionCore_eq_primeCore_of_prime_kernel prime _ prime_kernel] at quotient_mem
  exact primeCore_le_actionCore prime action quotient_mem

theorem primeStable_of_frattini_quotient_image {actors target : Type*} [Group actors]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (prime_target : IsPGroup prime target) (action : actors →* MulAut target)
    (stable_quotient : primeStable prime (quotientAction (frattini target) action.range.subtype)) :
    primeStable prime action :=
  primeStable_of_range_action prime action
    (primeStable_of_frattini_quotient_faithful prime prime_target action.range.subtype
      Subtype.val_injective stable_quotient)

end CFSG.OrderReductions.ActionImageCore
