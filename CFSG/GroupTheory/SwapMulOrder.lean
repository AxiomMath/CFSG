module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GroupTheory

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem orderOf_swap_mul_swap_same_mem (x y z : α) :
    orderOf (Equiv.swap x y * Equiv.swap x z) ∈ ({1, 2, 3} : Set ℕ) := by
  by_cases hxy : x = y
  · subst hxy
    have hx : orderOf (Equiv.swap x z) ∈ ({1, 2, 3} : Set ℕ) := by
      by_cases hxz : x = z
      · subst hxz
        rw [Equiv.swap_self]
        change orderOf (1 : Equiv.Perm α) ∈ ({1, 2, 3} : Set ℕ)
        simp
      · rw [(Equiv.Perm.swap_isSwap_iff.mpr hxz).orderOf]
        simp
    rw [Equiv.swap_self]
    change orderOf (Equiv.swap x z) ∈ ({1, 2, 3} : Set ℕ)
    exact hx
  by_cases hxz : x = z
  · subst hxz
    have hx : orderOf (Equiv.swap x y) ∈ ({1, 2, 3} : Set ℕ) := by
      rw [(Equiv.Perm.swap_isSwap_iff.mpr hxy).orderOf]
      simp
    rw [Equiv.swap_self]
    change orderOf (Equiv.swap x y) ∈ ({1, 2, 3} : Set ℕ)
    exact hx
  by_cases hyz : y = z
  · subst hyz
    rw [Equiv.swap_mul_self]
    simp
  rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz).orderOf]
  simp

theorem orderOf_mul_mem_of_isSwap {σ τ : Equiv.Perm α} (hσ : σ.IsSwap) (hτ : τ.IsSwap) :
    orderOf (σ * τ) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, d, hcd, rfl⟩ := hτ
  by_cases hac : a = c
  · subst hac
    exact orderOf_swap_mul_swap_same_mem a b d
  by_cases had : a = d
  · subst had
    rw [Equiv.swap_comm c a]
    exact orderOf_swap_mul_swap_same_mem a b c
  by_cases hbc : b = c
  · subst hbc
    rw [Equiv.swap_comm a b]
    exact orderOf_swap_mul_swap_same_mem b a d
  by_cases hbd : b = d
  · subst hbd
    rw [Equiv.swap_comm a b, Equiv.swap_comm c b]
    exact orderOf_swap_mul_swap_same_mem b a c
  have hcomm : Commute (Equiv.swap a b) (Equiv.swap c d) :=
    Equiv.Perm.Disjoint.commute (fun z => by
      by_cases hz : z = a ∨ z = b
      · right
        rcases hz with rfl | rfl
        · exact Equiv.swap_apply_of_ne_of_ne hac had
        · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
      · left
        push Not at hz
        exact Equiv.swap_apply_of_ne_of_ne hz.1 hz.2)
  have h2 : (Equiv.swap a b * Equiv.swap c d) ^ 2 = 1 := by
    rw [hcomm.mul_pow, pow_two (Equiv.swap a b), pow_two (Equiv.swap c d),
      Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · rw [h]; simp
  · rw [h]; simp

end CFSG.GroupTheory

end
