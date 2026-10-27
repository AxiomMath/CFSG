module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {G : Type*} [Group G]

@[expose] def primaryComponent (B : Subgroup G) (hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (p : ℕ) :
    Subgroup G where
  carrier := {x | x ∈ B ∧ ∃ k : ℕ, x ^ (p ^ k) = 1}
  one_mem' := ⟨B.one_mem, 0, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨haB, i, hai⟩ ⟨hbB, j, hbj⟩
    refine ⟨B.mul_mem haB hbB, i + j, ?_⟩
    have hc : Commute a b := hB a haB b hbB
    rw [hc.mul_pow, pow_add, pow_mul, hai, one_pow, mul_comm (p ^ i) (p ^ j), pow_mul, hbj,
      one_pow, one_mul]
  inv_mem' := by
    rintro a ⟨haB, i, hai⟩
    exact ⟨B.inv_mem haB, i, by rw [inv_pow, hai, inv_one]⟩

theorem mem_primaryComponent {B : Subgroup G} {hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} {p : ℕ}
    {x : G} : x ∈ primaryComponent B hB p ↔ x ∈ B ∧ ∃ k : ℕ, x ^ (p ^ k) = 1 := Iff.rfl

theorem primaryComponent_le {B : Subgroup G} {hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} {p : ℕ} :
    primaryComponent B hB p ≤ B := fun _ hx => hx.1

theorem primaryComponent_conj {B : Subgroup G} {hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} {p : ℕ}
    {g a : G} (hg : ∀ b ∈ B, g * b * g⁻¹ ∈ B) (ha : a ∈ primaryComponent B hB p) :
    g * a * g⁻¹ ∈ primaryComponent B hB p := by
  obtain ⟨haB, i, hai⟩ := ha
  refine ⟨hg a haB, i, ?_⟩
  rw [conj_pow, hai]
  group

theorem isPGroup_primaryComponent {B : Subgroup G} {hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a} {p : ℕ}
    (hp : p.Prime) : IsPGroup p (primaryComponent B hB p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  obtain ⟨-, k, hk⟩ := id hx
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp h1
  exact ⟨m, by rw [Subgroup.orderOf_mk]; exact hm⟩

theorem mem_primaryComponent_of_orderOf {B : Subgroup G} {hB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a}
    {p : ℕ} {x : G} (hx : x ∈ B) {m : ℕ} (hm : orderOf x = p ^ m) :
    x ∈ primaryComponent B hB p :=
  ⟨hx, m, by rw [← hm]; exact pow_orderOf_eq_one x⟩

end CFSG.GH74.Uniqueness
