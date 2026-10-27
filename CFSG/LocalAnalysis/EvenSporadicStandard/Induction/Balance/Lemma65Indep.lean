module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup

theorem two_mul_card_le_of_lt {Γ : Type*} [Group Γ] [Finite Γ] {A B : Subgroup Γ} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le h.le
  have hB : 0 < Nat.card B := Nat.card_pos
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hc
    exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (le_of_eq hc))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact hB.ne' hc
  have h2c : 2 ≤ c := by omega
  rw [hc]
  calc 2 * Nat.card A ≤ c * Nat.card A := Nat.mul_le_mul_right _ h2c
    _ = Nat.card A * c := mul_comm _ _

theorem pow_card_le_card_closure {Γ : Type*} [Group Γ] [Finite Γ] {S : Set Γ}
    (h : ∀ w ∈ S, w ∉ Subgroup.closure (S \ {w})) (T : Finset Γ) (hT : (T : Set Γ) ⊆ S) :
    2 ^ T.card ≤ Nat.card (Subgroup.closure (T : Set Γ)) := by
  classical
  revert hT
  refine Finset.induction_on T ?_ ?_
  · intro _
    simp
  · intro w T hw ih hT
    have hTS : (T : Set Γ) ⊆ S := fun x hx => hT (by simp [hx])
    have hwS : w ∈ S := hT (by simp)
    have hsub : Subgroup.closure (T : Set Γ) ≤ Subgroup.closure (S \ {w}) :=
      Subgroup.closure_mono fun x hx =>
        ⟨hTS hx, fun hxw => hw (by rw [Set.mem_singleton_iff] at hxw; rw [← hxw]; exact hx)⟩
    have hlt : Subgroup.closure (T : Set Γ) <
        Subgroup.closure ((insert w T : Finset Γ) : Set Γ) := by
      refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun heq => h w hwS ?_
      have hwmem : w ∈ Subgroup.closure ((insert w T : Finset Γ) : Set Γ) :=
        Subgroup.subset_closure (by simp)
      rw [← heq] at hwmem
      exact hsub hwmem
    calc 2 ^ (insert w T).card = 2 * 2 ^ T.card := by
          rw [Finset.card_insert_of_notMem hw, pow_succ, mul_comm]
      _ ≤ 2 * Nat.card (Subgroup.closure (T : Set Γ)) := Nat.mul_le_mul_left 2 (ih hTS)
      _ ≤ Nat.card (Subgroup.closure ((insert w T : Finset Γ) : Set Γ)) :=
          two_mul_card_le_of_lt hlt

end CFSG.EvenSporadicStandard.Induction.Balance
