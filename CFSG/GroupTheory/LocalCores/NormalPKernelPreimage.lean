module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.LocalCores

variable {H : Type*} [Group H] [Finite H]

theorem normal_p_kernel_core_preimage {p : ℕ} (hp : p.Prime) (N : Subgroup H) [N.Normal]
    (hN : IsPGroup p N) :
    (piCore ({⟨p, hp⟩} : Set Nat.Primes) (H ⧸ N)).comap (QuotientGroup.mk' N) =
      piCore ({⟨p, hp⟩} : Set Nat.Primes) H := by
  have : Fact p.Prime := ⟨hp⟩
  have hNπ : IsPiSubgroup ({⟨p, hp⟩} : Set Nat.Primes) N := by
    intro q hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN
    rw [hk] at hq
    exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow hq))
  have hsurj := QuotientGroup.mk'_surjective N
  apply le_antisymm
  · refine le_piCore_of_normal (Subgroup.Normal.comap inferInstance _) ?_
    refine isPiSubgroup_of_map_of_inf_ker (QuotientGroup.mk' N) ?_ ?_
    · rw [Subgroup.map_comap_eq_self_of_surjective hsurj]
      exact piCore_isPiSubgroup _
    · rw [QuotientGroup.ker_mk']
      exact hNπ.of_le inf_le_right
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_piCore_of_normal (Subgroup.Normal.map inferInstance _ hsurj)
      (isPiSubgroup_map (piCore_isPiSubgroup _) _)

end CFSG.LocalCores
