module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open Equiv Equiv.Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem eq_three_of_mem_cycleType {σ : Perm α} (h3 : orderOf σ = 3) {m : ℕ}
    (hm : m ∈ σ.cycleType) : m = 3 := by
  have h2 : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hm
  have hd : m ∣ 3 := h3 ▸ Equiv.Perm.dvd_of_mem_cycleType hm
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · omega
  · exact h

theorem cycleType_eq_replicate_three {σ : Perm α} (h3 : orderOf σ = 3) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
  Multiset.eq_replicate_card.mpr fun _ hm => eq_three_of_mem_cycleType h3 hm

end CFSG.HardMathSupport.RichardWeiss.Proving

end
