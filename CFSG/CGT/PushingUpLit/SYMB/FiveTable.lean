module

public import CFSG.CGT.PushingUpLit.SYMB.FiveY
public import CFSG.CGT.PushingUpLit.SYMB.Delta5Swaps

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open Equiv

section Pts

variable {a b c d : Fin 5}

theorem swap_ne_one (hab : a ≠ b) : swap a b ≠ 1 := fun h => by
  have := congrArg (fun f : Perm (Fin 5) => f a) h
  simp only [swap_apply_left, Perm.one_apply] at this
  exact hab this.symm

theorem swap_ne_swap (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) : swap a b ≠ swap c d := fun h => by
  have := congrArg (fun f : Perm (Fin 5) => f a) h
  simp only [swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne hac had] at this
  exact hab this.symm

theorem swap_comm_swap (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d = swap c d * swap a b := by
  have h : ∀ a b c d : Fin 5, a ≠ c → a ≠ d → b ≠ c → b ≠ d →
      swap a b * swap c d = swap c d * swap a b := by
    set_option synthInstance.maxSize 2000 in decide +kernel
  exact h a b c d hac had hbc hbd

theorem swap_mul_swap_ne_one (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    swap a b * swap c d ≠ 1 := fun h => by
  have := congrArg (fun f : Perm (Fin 5) => f a) h
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left, Perm.one_apply] at this
  exact hab this.symm

theorem swap_pair_sq (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (swap a b * swap c d) * (swap a b * swap c d) = 1 := by
  have hc := swap_comm_swap hac had hbc hbd
  calc (swap a b * swap c d) * (swap a b * swap c d)
      = swap a b * (swap c d * swap a b) * swap c d := by simp only [mul_assoc]
    _ = swap a b * (swap a b * swap c d) * swap c d := by rw [← hc]
    _ = (swap a b * swap a b) * (swap c d * swap c d) := by simp only [mul_assoc]
    _ = 1 := by rw [swap_mul_self, swap_mul_self, one_mul]

theorem table_good (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) {P : Subgroup (Perm (Fin 5))}
    (hP : P = ⊥ ∨ P = Subgroup.zpowers (swap a b) ∨ P = Subgroup.zpowers (swap c d) ∨
      P = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) :
    Nat.card ↥P * Nat.card ↥(Delta5Swaps.Fixed P) = 16 := by
  rcases hP with rfl | rfl | rfl | rfl
  · rw [Subgroup.card_bot, Delta5Swaps.card_Fixed_bot]
  · rw [card_zpowers_invol (swap_mul_self a b) (swap_ne_one hab), Delta5Swaps.card_Fixed_swap hab]
  · rw [card_zpowers_invol (swap_mul_self c d) (swap_ne_one hcd), Delta5Swaps.card_Fixed_swap hcd]
  · rw [card_pair (swap_mul_self a b) (swap_mul_self c d) (swap_comm_swap hac had hbc hbd)
      (swap_ne_swap hab hac had) (swap_ne_one hab) (swap_ne_one hcd),
      Delta5Swaps.card_Fixed_pair hab hcd hac had hbc hbd]

theorem table_prod (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) :
    Nat.card ↥(Subgroup.zpowers (swap a b * swap c d)) *
      Nat.card ↥(Delta5Swaps.Fixed (Subgroup.zpowers (swap a b * swap c d))) = 8 := by
  rw [card_zpowers_invol (swap_pair_sq hac had hbc hbd) (swap_mul_swap_ne_one hab hac had),
    Delta5Swaps.card_Fixed_prod hab hcd hac had hbc hbd]

theorem classify (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    {P : Subgroup (Perm (Fin 5))} (hP : P ≤ Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) :
    (P = ⊥ ∨ P = Subgroup.zpowers (swap a b) ∨ P = Subgroup.zpowers (swap c d) ∨
      P = Subgroup.zpowers (swap a b) ⊔ Subgroup.zpowers (swap c d)) ∨
      P = Subgroup.zpowers (swap a b * swap c d) := by
  rcases subgroup_of_pair (swap_mul_self a b) (swap_mul_self c d) (swap_comm_swap hac had hbc hbd)
    hP with h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr h
  · exact Or.inl (Or.inr (Or.inr (Or.inr h)))

end Pts

end CFSG.CGT.PushingUpLit.SYMB
