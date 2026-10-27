module

public import CFSG.CGT.PushingUpLit.BHSSym.SylowTransfer
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.CGT.PushingUpLit.BHSSym

open Equiv Equiv.Perm

variable {m : ℕ} {T : Subgroup (Perm (Fin m))}

theorem eq_of_swap_mem (hT2 : IsPGroup 2 T) {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c)
    (h1 : swap a b ∈ T) (h2 : swap a c ∈ T) : b = c := by
  by_contra hbc
  have h3 : (swap a b * swap a c).IsThreeCycle := isThreeCycle_swap_mul_swap_same hab hac hbc
  have hmem : swap a b * swap a c ∈ T := T.mul_mem h1 h2
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT2 ⟨_, hmem⟩
  rw [Subgroup.orderOf_mk, h3.orderOf] at hk
  have h4 : 3 ∣ 2 ^ k := by rw [← hk]
  have := Nat.prime_three.dvd_of_dvd_pow h4
  omega

theorem isPGroup_zpowers_swap {α : Type*} [DecidableEq α] [Fintype α] {a b : α} (hab : a ≠ b) :
    IsPGroup 2 (Subgroup.zpowers (swap a b)) := by
  have h2 : orderOf (swap a b) = 2 := orderOf_eq_prime (by simp [sq]) (by
    intro h
    have := congrArg (fun f => f a) h
    simp at this
    exact hab this.symm)
  have := Nat.card_zpowers (swap a b)
  rw [h2] at this
  exact IsPGroup.of_card (n := 1) (by simpa using this)

theorem exists_swap_mem_of_invariant (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    {A : Set (Fin m)} (hA : ∀ t ∈ T, ∀ x, t x ∈ A ↔ x ∈ A) {a b : Fin m} (ha : a ∈ A)
    (hb : b ∈ A) (hab : a ≠ b) : ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ swap p q ∈ T := by
  obtain ⟨h, hh, hconj⟩ := exists_conj_le_of_isPGroup hT2 hTidx (le_setStab hA)
    (isPGroup_zpowers_swap hab) (Subgroup.zpowers_le.2 (swap_mem_setStab ha hb))
  have h1 := hconj (swap a b) (Subgroup.mem_zpowers _)
  rw [← swap_apply_apply] at h1
  refine ⟨h a, (hh a).2 ha, h b, (hh b).2 hb, fun e => hab (h.injective e), ?_⟩
  simpa [swap_apply_apply, mul_assoc] using h1

theorem exists_isFixed (hm : Odd m) (hT2 : IsPGroup 2 T) : ∃ a : Fin m, ∀ t ∈ T, t a = a := by
  have hodd : ¬ 2 ∣ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.not_even_iff_odd.2 hm |> fun h => by simpa [even_iff_two_dvd] using h
  obtain ⟨a, ha⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card (α := Fin m) hodd
  exact ⟨a, fun t ht => ha ⟨t, ht⟩⟩

theorem eq_of_isFixed (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) {a b : Fin m}
    (ha : ∀ t ∈ T, t a = a) (hb : ∀ t ∈ T, t b = b) : a = b := by
  by_contra hab
  have hA : ∀ t ∈ T, ∀ x, t x ∈ ({a, b} : Set (Fin m)) ↔ x ∈ ({a, b} : Set (Fin m)) := by
    intro t ht x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · left
        exact t.injective (h.trans (ha t ht).symm)
      · right
        exact t.injective (h.trans (hb t ht).symm)
    · rintro (h | h)
      · left
        rw [h]
        exact ha t ht
      · right
        rw [h]
        exact hb t ht
  obtain ⟨p, hp, q, hq, hpq, hs⟩ := exists_swap_mem_of_invariant hT2 hTidx hA
    (Set.mem_insert a {b}) (Set.mem_insert_of_mem a (Set.mem_singleton b)) hab
  have hs' : swap a b ∈ T := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · exact hs
    · rw [swap_comm]
      exact hs
    · exact absurd rfl hpq
  have := ha _ hs'
  rw [swap_apply_left] at this
  exact hab this.symm

theorem exists_edge (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) {i₀ : Fin m}
    (hi₀ : ∀ t ∈ T, t i₀ = i₀) {a : Fin m} (ha : a ≠ i₀) :
    ∃ b, a ≠ b ∧ swap a b ∈ T := by
  have hna : ¬ ∀ t ∈ T, t a = a := fun h => ha (eq_of_isFixed hT2 hTidx h hi₀)
  push Not at hna
  obtain ⟨t₀, ht₀, hat⟩ := hna
  set A : Set (Fin m) := {x | ∃ s ∈ T, s a = x} with hAdef
  have hA : ∀ t ∈ T, ∀ x, t x ∈ A ↔ x ∈ A := by
    intro t ht x
    constructor
    · rintro ⟨s, hs, hsx⟩
      refine ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, ?_⟩
      simp [Perm.mul_apply, hsx]
    · rintro ⟨s, hs, hsx⟩
      exact ⟨t * s, T.mul_mem ht hs, by simp [Perm.mul_apply, hsx]⟩
  have haA : a ∈ A := ⟨1, T.one_mem, rfl⟩
  have htA : t₀ a ∈ A := ⟨t₀, ht₀, rfl⟩
  obtain ⟨p, ⟨s, hs, hsp⟩, q, hq, hpq, hpqT⟩ :=
    exists_swap_mem_of_invariant hT2 hTidx hA haA htA hat.symm
  refine ⟨s⁻¹ q, ?_, ?_⟩
  · intro h
    apply hpq
    rw [← hsp, h]
    simp
  · have h1 : s⁻¹ * swap p q * s ∈ T := T.mul_mem (T.mul_mem (T.inv_mem hs) hpqT) hs
    have hsa : s⁻¹ p = a := by rw [← hsp]; simp
    have h2 : swap a (s⁻¹ q) = s⁻¹ * swap p q * s := by
      have := swap_apply_apply s⁻¹ p q
      rw [inv_inv] at this
      rw [← hsa]
      exact this
    rw [h2]
    exact h1

end CFSG.CGT.PushingUpLit.BHSSym
