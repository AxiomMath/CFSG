module

public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GroupTheory.SteinbergBS

open Subgroup CFSG.LocalCores
open scoped Pointwise

variable {H : Type*} [Group H]

theorem isPiSubgroup_compl_iff {q : ℕ} (hq : q.Prime) (K : Subgroup H) :
    IsPiSubgroup {r : Nat.Primes | (r : ℕ) ≠ q} K ↔ Nat.Coprime q (Nat.card K) := by
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  constructor
  · intro hK hdvd
    exact hK ⟨q, hq⟩ hdvd rfl
  · intro hK r hr hrq
    exact hK (hrq ▸ hr)

end CFSG.GroupTheory.SteinbergBS
