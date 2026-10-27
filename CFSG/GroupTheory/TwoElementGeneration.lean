module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

open Equiv

variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem exists_twoElem_mem_map (f : G →* H) {M : Subgroup G} {m : G} (hm : m ∈ M)
    (hσ : f m * f m = 1) :
    ∃ m' ∈ M, (∃ c : ℕ, m' ^ 2 ^ c = 1) ∧ f m' = f m := by
  obtain ⟨a, k, hk_odd, hk_eq⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  refine ⟨m ^ k, M.pow_mem hm k, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm k (2 ^ a), ← hk_eq, pow_orderOf_eq_one]
  · rw [map_pow]
    obtain ⟨j, rfl⟩ := hk_odd
    rw [show (f m) ^ (2 * j + 1) = ((f m) ^ 2) ^ j * f m by rw [pow_succ, pow_mul]]
    rw [show (f m) ^ 2 = 1 by rw [pow_two]; exact hσ, one_pow, one_mul]

theorem closure_involutions_perm_eq_top {Δ : Type*} [Finite Δ] :
    Subgroup.closure {σ : Equiv.Perm Δ | σ * σ = 1} = ⊤ := by
  classical
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap]
  refine Subgroup.closure_mono ?_
  rintro σ ⟨x, y, hxy, rfl⟩
  show Equiv.swap x y * Equiv.swap x y = 1
  rw [Equiv.swap_mul_self]

end CFSG.GroupTheory
