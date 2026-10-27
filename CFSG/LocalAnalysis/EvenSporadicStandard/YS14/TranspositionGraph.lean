module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.YS14

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def evenSub (Q : Set G) : Subgroup G :=
  Subgroup.closure {x | ∃ p ∈ Q, ∃ q ∈ Q, x = p * q}

theorem mul_mem_evenSub {Q : Set G} {p q : G} (hp : p ∈ Q) (hq : q ∈ Q) :
    p * q ∈ evenSub Q :=
  Subgroup.subset_closure ⟨p, hp, q, hq, rfl⟩

theorem mul_mem_commutator_evenSub {Q : Set G} {p q s : G} (hp : p ∈ Q) (hq : q ∈ Q)
    (hs : s ∈ Q) (hpp : p * p = 1) (hqq : q * q = 1) (hss : s * s = 1) (h3 : (p * q) ^ 3 = 1)
    (hsp : s * p = p * s) (hsq : s * q = q * s) : p * q ∈ ⁅evenSub Q, evenSub Q⁆ := by
  have hg : p * q ∈ evenSub Q := mul_mem_evenSub hp hq
  have hh : p * s ∈ evenSub Q := mul_mem_evenSub hp hs
  have hp1 : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  have hq1 : q⁻¹ = q := inv_eq_of_mul_eq_one_right hqq
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hspq : s * p * q * s = p * q := by
    calc s * p * q * s = p * s * q * s := by rw [hsp]
      _ = p * (s * q) * s := by group
      _ = p * (q * s) * s := by rw [hsq]
      _ = p * q * (s * s) := by group
      _ = p * q := by rw [hss, mul_one]
  have hinv : p * s * (p * q) * (p * s)⁻¹ = (p * q)⁻¹ := by
    calc p * s * (p * q) * (p * s)⁻¹ = p * s * (p * q) * (s⁻¹ * p⁻¹) := by rw [mul_inv_rev]
      _ = p * s * (p * q) * (s * p) := by rw [hs1, hp1]
      _ = p * (s * p * q * s) * p := by group
      _ = p * (p * q) * p := by rw [hspq]
      _ = (p * p) * q * p := by group
      _ = q * p := by rw [hpp, one_mul]
      _ = (p * q)⁻¹ := by rw [mul_inv_rev, hq1, hp1]
  have hcomm : ⁅p * s, p * q⁆ = p * q := by
    rw [commutatorElement_def, hinv]
    have key : ∀ g : G, g⁻¹ * g⁻¹ * g ^ 3 = g := fun g => by group
    calc (p * q)⁻¹ * (p * q)⁻¹ = (p * q)⁻¹ * (p * q)⁻¹ * ((p * q) ^ 3) := by rw [h3, mul_one]
      _ = p * q := key (p * q)
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator hh hg

theorem evenSub_perfect (Q : Set G) (hsq : ∀ p ∈ Q, p * p = 1)
    (hcube : ∀ p ∈ Q, ∀ q ∈ Q, p * q ≠ q * p → (p * q) ^ 3 = 1)
    (hthird : ∀ p ∈ Q, ∀ q ∈ Q, p * q ≠ q * p → ∃ s ∈ Q, s * p = p * s ∧ s * q = q * s)
    (hconn : ∀ p ∈ Q, ∀ q ∈ Q,
      Relation.ReflTransGen (fun a b => a ∈ Q ∧ b ∈ Q ∧ a * b ≠ b * a) p q) :
    evenSub Q ≤ ⁅evenSub Q, evenSub Q⁆ := by
  have hstep : ∀ a ∈ Q, ∀ b ∈ Q, a * b ≠ b * a → a * b ∈ ⁅evenSub Q, evenSub Q⁆ := by
    intro a ha b hb hab
    obtain ⟨s, hs, hsa, hsb⟩ := hthird a ha b hb hab
    exact mul_mem_commutator_evenSub ha hb hs (hsq a ha) (hsq b hb) (hsq s hs)
      (hcube a ha b hb hab) hsa hsb
  have hall : ∀ p ∈ Q, ∀ q : G, Relation.ReflTransGen
      (fun a b => a ∈ Q ∧ b ∈ Q ∧ a * b ≠ b * a) p q → q ∈ Q →
      p * q ∈ ⁅evenSub Q, evenSub Q⁆ := by
    intro p hp q hpq
    induction hpq with
    | refl => intro _; rw [hsq p hp]; exact one_mem _
    | @tail b c _ hbc ih =>
      intro hc
      obtain ⟨hb, -, hne⟩ := hbc
      have e : p * c = (p * b) * (b * c) := by
        calc p * c = p * (b * b) * c := by rw [hsq b hb, mul_one]
          _ = (p * b) * (b * c) := by group
      rw [e]
      exact Subgroup.mul_mem _ (ih hb) (hstep b hb c hc hne)
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨p, hp, q, hq, rfl⟩
  exact hall p hp q (hconn p hp q hq) hq

end CFSG.EvenSporadicStandard.YS14
