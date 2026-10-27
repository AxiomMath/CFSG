module

public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphismKernel
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG

open FiveTransitive.CharacteristicAutomorphism

universe u

@[expose] def characteristicRestrictionQuotient {G : Type u} [Group G]
    (N : Subgroup G) [N.Characteristic] :
    MulAut G →* MulAut N × MulAut (G ⧸ N) :=
  (restrict N).prod (quotient N)

theorem characteristicRestrictionQuotient_ker {G : Type u} [Group G]
    (N : Subgroup G) [N.Characteristic] :
    (characteristicRestrictionQuotient N).ker =
      (restrict N).ker ⊓ (quotient N).ker :=
  MonoidHom.ker_prod (restrict N) (quotient N)

theorem characteristic_joint_kernel_isPGroup {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) [N.Characteristic]
    (hN : IsPGroup p N) :
    IsPGroup p ((restrict N).ker ⊓ (quotient N).ker : Subgroup (MulAut G)) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hcard⟩ := hN.exists_card_eq
  apply (isPGroup_iff_primeFactors_card_subset hp.ne_zero).mpr
  intro q hq
  obtain ⟨hqprime, hqdivides, _⟩ := Nat.mem_primeFactors.mp hq
  by_cases hqp : q = p
  · subst q
    exact Nat.mem_primeFactors.mpr ⟨hp, dvd_refl p, hp.ne_zero⟩
  · have hcoprime : q.Coprime (Nat.card N) := by
      rw [hcard]
      simpa only [pow_one] using Nat.coprime_pow_primes 1 n hqprime hp hqp
    exact False.elim
      (FiveTransitive.CharacteristicAutomorphismKernel.prime_not_dvd
        N q hqprime hcoprime hqdivides)

theorem characteristic_automorphism_isPGroup {G : Type u} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (N : Subgroup G) [N.Characteristic]
    (hN : IsPGroup p N) (hRestrict : IsPGroup p (MulAut N))
    (hQuotient : IsPGroup p (MulAut (G ⧸ N))) : IsPGroup p (MulAut G) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi⟩ := hRestrict.exists_card_eq
  obtain ⟨j, hj⟩ := hQuotient.exists_card_eq
  have hproduct : IsPGroup p (MulAut N × MulAut (G ⧸ N)) :=
    IsPGroup.of_card (n := i + j) (by rw [Nat.card_prod, hi, hj, pow_add])
  have hkernel : IsPGroup p (characteristicRestrictionQuotient N).ker := by
    rw [characteristicRestrictionQuotient_ker]
    exact characteristic_joint_kernel_isPGroup p hp N hN
  have hfull := (hproduct.to_subgroup ⊤).comap_of_ker_isPGroup
    (characteristicRestrictionQuotient N) hkernel
  rw [Subgroup.comap_top] at hfull
  exact hfull.of_equiv Subgroup.topEquiv

end CFSG
