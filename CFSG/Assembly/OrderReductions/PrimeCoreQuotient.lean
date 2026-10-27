module

public import CFSG.Assembly.OrderReductions.PrimeCore

public section

namespace CFSG.OrderReductions.PrimeCoreQuotient

open CFSG.OrderReductions.PrimeCore

theorem comap_primeCore_eq_of_prime_kernel {source target : Type*} [Group source] [Group target]
    (prime : ℕ) (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (prime_kernel : IsPGroup prime homomorphism.ker) :
    (primeCore prime target).comap homomorphism = primeCore prime source := by
  have preimage_prime := (primeCore_isPGroup prime target).comap_of_ker_isPGroup homomorphism prime_kernel
  exact le_antisymm (normal_le_primeCore prime _ preimage_prime)
    (Subgroup.map_le_iff_le_comap.mp (map_core_le_of_surjective prime homomorphism surjective))

theorem map_primeCore_eq_of_prime_kernel {source target : Type*} [Group source] [Group target]
    (prime : ℕ) (homomorphism : source →* target) (surjective : Function.Surjective homomorphism)
    (prime_kernel : IsPGroup prime homomorphism.ker) :
    (primeCore prime source).map homomorphism = primeCore prime target := by
  rw [← comap_primeCore_eq_of_prime_kernel prime homomorphism surjective prime_kernel]
  exact Subgroup.map_comap_eq_self_of_surjective surjective _

theorem primeCore_quotient_eq_bot {group : Type*} [Group group] (prime : ℕ) :
    primeCore prime (group ⧸ primeCore prime group) = ⊥ := by
  let core := primeCore prime group
  let projection := QuotientGroup.mk' core
  have kernel_prime : IsPGroup prime projection.ker := by
    rw [QuotientGroup.ker_mk']
    exact primeCore_isPGroup prime group
  rw [← map_primeCore_eq_of_prime_kernel prime projection (QuotientGroup.mk'_surjective core) kernel_prime]
  exact QuotientGroup.map_mk'_self core

end CFSG.OrderReductions.PrimeCoreQuotient
