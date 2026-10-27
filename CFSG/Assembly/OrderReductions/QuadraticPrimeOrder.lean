module

public import CFSG.Assembly.OrderReductions.ActionPrimeCore

public section

namespace CFSG.OrderReductions.QuadraticPrimeOrder

open CFSG.OrderReductions.ClassTwoCubic CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore

theorem quadratic_automorphism_pow_apply {group : Type*} [Group group]
    (automorphism : MulAut group)
    (quadratic : ∀ element : group, difference automorphism (difference automorphism element) = 1)
    (exponent : ℕ) (element : group) :
    (automorphism ^ exponent) element = element * difference automorphism element ^ exponent := by
  have fixed : automorphism (difference automorphism element) = difference automorphism element := by
    have equal := quadratic element
    change (difference automorphism element)⁻¹ * automorphism (difference automorphism element) = 1 at equal
    exact (inv_mul_eq_one.mp equal).symm
  induction exponent with
  | zero =>
      change element = element * difference automorphism element ^ 0
      rw [pow_zero, mul_one]
  | succ exponent induction_hypothesis =>
      rw [pow_succ']
      change automorphism ((automorphism ^ exponent) element) = _
      rw [induction_hypothesis, map_mul, map_pow, fixed]
      have automorphism_element : automorphism element = element * difference automorphism element := by
        dsimp [difference]
        group
      rw [automorphism_element, pow_succ']
      exact mul_assoc _ _ _

theorem quadratic_automorphism_pow_card {group : Type*} [Group group]
    (automorphism : MulAut group)
    (quadratic : ∀ element : group, difference automorphism (difference automorphism element) = 1) :
    automorphism ^ Nat.card group = 1 := by
  ext element
  rw [quadratic_automorphism_pow_apply automorphism quadratic, pow_card_eq_one', mul_one]
  rfl

theorem quadratic_actor_pow_mem_kernel {actors target : Type*} [Group actors] [Group target] [Finite target]
    (prime : ℕ) [Fact (Nat.Prime prime)] (prime_target : IsPGroup prime target)
    (action : actors →* MulAut target) (actor : actors) (acts_quadratically : quadratic action actor) :
    ∃ exponent : ℕ, actor ^ prime ^ exponent ∈ action.ker := by
  obtain ⟨exponent, card_eq⟩ := prime_target.exists_card_eq
  have inverse_pow := quadratic_automorphism_pow_card (action actor⁻¹) acts_quadratically
  rw [card_eq, ← map_pow] at inverse_pow
  have kernel_inverse : (actor⁻¹) ^ prime ^ exponent ∈ action.ker := MonoidHom.mem_ker.mpr inverse_pow
  refine ⟨exponent, ?_⟩
  simpa only [inv_pow, inv_inv] using action.ker.inv_mem kernel_inverse

theorem prime_element_mem_normal_sylow {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) [(sylow : Subgroup group).Normal]
    (element : group) {exponent : ℕ} (power_one : element ^ prime ^ exponent = 1) : element ∈ sylow := by
  have prime_cyclic : IsPGroup prime (Subgroup.zpowers element) := by
    apply IsPGroup.of_card_dvd_pow
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one power_one
  obtain ⟨containing, contains⟩ := prime_cyclic.exists_le_sylow
  have : Unique (Sylow prime group) := Sylow.unique_of_normal sylow inferInstance
  have equal : containing = sylow := Subsingleton.elim _ _
  rw [← equal]
  exact contains (Subgroup.mem_zpowers element)

theorem primeStable_of_normal_sylow {actors target : Type*} [Group actors] [Finite actors]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (sylow : Sylow prime actors) [(sylow : Subgroup actors).Normal]
    (prime_target : IsPGroup prime target) (action : actors →* MulAut target) :
    primeStable prime action := by
  intro actor acts_quadratically
  obtain ⟨exponent, kernel_mem⟩ := quadratic_actor_pow_mem_kernel prime prime_target action actor acts_quadratically
  let projection := QuotientGroup.mk' action.ker
  let image := sylow.mapSurjective (QuotientGroup.mk'_surjective action.ker)
  have : (image : Subgroup (actors ⧸ action.ker)).Normal := by
    rw [Sylow.coe_mapSurjective]
    exact (inferInstance : (sylow : Subgroup actors).Normal).map projection (QuotientGroup.mk'_surjective action.ker)
  have projection_pow : projection actor ^ prime ^ exponent = 1 := by
    rw [← map_pow]
    apply MonoidHom.mem_ker.mp
    rwa [QuotientGroup.ker_mk']
  have actor_image := prime_element_mem_normal_sylow prime image (projection actor) projection_pow
  change projection actor ∈ primeCore prime (actors ⧸ action.ker)
  exact normal_le_primeCore prime image image.isPGroup' actor_image

theorem exists_normal_sylow_in_subgroup {group : Type*} [Group group] [Finite group]
    (prime : ℕ) [Fact (Nat.Prime prime)] (sylow : Sylow prime group) [(sylow : Subgroup group).Normal]
    (subgroup : Subgroup group) :
    ∃ internal : Sylow prime subgroup, (internal : Subgroup subgroup).Normal := by
  let intersection := (sylow : Subgroup group).subgroupOf subgroup
  have intersection_prime : IsPGroup prime intersection :=
    sylow.isPGroup'.comap_of_injective subgroup.subtype Subtype.val_injective
  have not_divides : ¬ prime ∣ intersection.index := by
    change ¬ prime ∣ (sylow : Subgroup group).relIndex subgroup
    intro divides
    exact sylow.not_dvd_index (divides.trans ((sylow : Subgroup group).relIndex_dvd_index_of_normal subgroup))
  let internal := intersection_prime.toSylow not_divides
  refine ⟨internal, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact inferInstanceAs intersection.Normal

theorem subgroup_actions_primeStable_of_normal_sylow {group target : Type*} [Group group] [Finite group]
    [Group target] [Finite target] (prime : ℕ) [Fact (Nat.Prime prime)]
    (sylow : Sylow prime group) [(sylow : Subgroup group).Normal]
    (subgroup : Subgroup group) (prime_target : IsPGroup prime target) (action : subgroup →* MulAut target) :
    primeStable prime action := by
  obtain ⟨internal, normal⟩ := exists_normal_sylow_in_subgroup prime sylow subgroup
  have : (internal : Subgroup subgroup).Normal := normal
  exact primeStable_of_normal_sylow prime internal prime_target action

end CFSG.OrderReductions.QuadraticPrimeOrder
