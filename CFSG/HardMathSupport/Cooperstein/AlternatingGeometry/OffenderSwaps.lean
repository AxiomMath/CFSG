module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderMax
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

open Equiv

theorem orderOf_swap_mul_swap {Ω : Type*} [DecidableEq Ω] {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : orderOf (swap a b * swap a c) = 3 := by
  have h3 : (swap a b * swap a c) ^ 3 = 1 := by
    ext x
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.coe_one, id_eq]
    by_cases h1 : x = a
    · subst h1; simp [swap_apply_def, hbc, hab.symm, hac.symm, hbc.symm]
    · by_cases h2 : x = b
      · subst h2; simp [swap_apply_def, hab.symm, hac.symm, hbc, hbc.symm]
      · by_cases h3 : x = c
        · subst h3; simp [swap_apply_def, hab.symm, hac.symm, hbc, hbc.symm]
        · simp [swap_apply_def, h1, h2, h3]
  have hne : swap a b * swap a c ≠ 1 := by
    intro h
    have := congrArg (fun f : Perm Ω => f a) h
    simp [swap_apply_def, hab, hac, hbc, hab.symm, hac.symm, hbc.symm] at this
  exact orderOf_eq_prime h3 hne

theorem disjoint_swap_of_pGroup {Ω : Type*} [DecidableEq Ω] {P : Subgroup (Perm Ω)}
    (hP : IsPGroup 2 P) {s t : Perm Ω} (hs : s ∈ P) (ht : t ∈ P) (hs' : s.IsSwap)
    (ht' : t.IsSwap) (hne : s ≠ t) : Perm.Disjoint s t := by
  obtain ⟨a, b, hab, rfl⟩ := hs'
  obtain ⟨c, d, hcd, rfl⟩ := ht'
  have key : ∀ {x y z : Ω}, x ≠ y → x ≠ z → y ≠ z →
      swap x y ∈ P → swap x z ∈ P → False := by
    intro x y z hxy hxz hyz h1 h2
    obtain ⟨k, hk⟩ := hP (⟨swap x y, h1⟩ * ⟨swap x z, h2⟩ : P)
    have h3 : orderOf (swap x y * swap x z) = 3 := orderOf_swap_mul_swap hxy hxz hyz
    have h4 : orderOf (⟨swap x y, h1⟩ * ⟨swap x z, h2⟩ : P) = 3 := by
      rw [← h3, ← Subgroup.orderOf_coe]; rfl
    have h5 : orderOf (⟨swap x y, h1⟩ * ⟨swap x z, h2⟩ : P) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one hk
    rw [h4] at h5
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    omega
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd; exact (hne rfl).elim
    · exact (key hab hcd hbd hs ht).elim
  by_cases had : a = d
  · subst had
    rw [swap_comm c a] at ht hne ⊢
    by_cases hbc : b = c
    · subst hbc; exact (hne rfl).elim
    · exact (key hab hcd.symm hbc hs ht).elim
  by_cases hbc : b = c
  · subst hbc
    rw [swap_comm a b] at hs hne ⊢
    exact (key hab.symm hcd had hs ht).elim
  by_cases hbd : b = d
  · subst hbd
    rw [swap_comm a b] at hs hne ⊢
    rw [swap_comm c b] at ht hne ⊢
    exact (key hab.symm hcd.symm hac hs ht).elim
  ·
    intro x
    by_cases hx : x = a ∨ x = b
    · right
      exact swap_apply_of_ne_of_ne (by rintro rfl; rcases hx with rfl | rfl <;> simp_all)
        (by rintro rfl; rcases hx with rfl | rfl <;> simp_all)
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2

theorem commute_swap_of_pGroup {Ω : Type*} [DecidableEq Ω] {P : Subgroup (Perm Ω)}
    (hP : IsPGroup 2 P) {s t : Perm Ω} (hs : s ∈ P) (ht : t ∈ P) (hs' : s.IsSwap)
    (ht' : t.IsSwap) : Commute s t := by
  by_cases hne : s = t
  · subst hne; exact Commute.refl _
  · exact (disjoint_swap_of_pGroup hP hs ht hs' ht' hne).commute

theorem iSup_eq_closure_disjoint_swaps {Ω : Type*} [DecidableEq Ω] {P : Subgroup (Perm Ω)}
    (hP : IsPGroup 2 P) {ι : Type*} (A : ι → Subgroup (Perm Ω)) (hAP : ∀ i, A i ≤ P)
    (hA : ∀ i, ∃ T : Set (Perm Ω), (∀ t ∈ T, t.IsSwap) ∧ A i = Subgroup.closure T) :
    ∃ T : Set (Perm Ω), (∀ t ∈ T, t.IsSwap) ∧ (∀ s ∈ T, ∀ t ∈ T, s ≠ t → Perm.Disjoint s t) ∧
      (∀ t ∈ T, t ∈ P) ∧ ⨆ i, A i = Subgroup.closure T := by
  choose T hTs hAT using hA
  refine ⟨⋃ i, T i, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
    exact hTs i t hi
  · intro s hs t ht hne
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hs
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 ht
    refine disjoint_swap_of_pGroup hP ?_ ?_ (hTs i s hi) (hTs j t hj) hne
    · exact hAP i (hAT i ▸ Subgroup.subset_closure hi)
    · exact hAP j (hAT j ▸ Subgroup.subset_closure hj)
  · intro t ht
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
    exact hAP i (hAT i ▸ Subgroup.subset_closure hi)
  · rw [Subgroup.closure_iUnion]
    exact iSup_congr fun i => hAT i

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
