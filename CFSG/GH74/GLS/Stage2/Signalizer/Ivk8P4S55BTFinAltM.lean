module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTFinAltW
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAltW

open Equiv Equiv.Perm Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
theorem mem_closure_list {S : List (Perm α)} {x t : Perm α} (h : x = t) (ht : t ∈ S) :
    x ∈ closure {x | x ∈ S} :=
  h ▸ subset_closure ht

omit [Fintype α] [DecidableEq α] in
theorem mem_closure_one {a : Perm α} {l : List (Perm α)} : a ∈ closure {x | x ∈ a :: l} :=
  subset_closure (List.Mem.head _)

omit [Fintype α] [DecidableEq α] in
theorem mem_closure_two {a b : Perm α} {l : List (Perm α)} :
    b ∈ closure {x | x ∈ a :: b :: l} :=
  subset_closure (List.Mem.tail _ (List.Mem.head _))

omit [Fintype α] [DecidableEq α] in
theorem mem_closure_three {a b c : Perm α} {l : List (Perm α)} :
    c ∈ closure {x | x ∈ a :: b :: c :: l} :=
  subset_closure (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

omit [Fintype α] [DecidableEq α] in
theorem mem_closure_four {a b c d : Perm α} {l : List (Perm α)} :
    d ∈ closure {x | x ∈ a :: b :: c :: d :: l} :=
  subset_closure (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

theorem sign_swap_mul_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    Perm.sign (swap a b * swap c d) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
  rfl

theorem altWit_m4 : AltWit 2 (swap (0 : Fin 4) 2 * swap 0 1) := by
  refine altWit_of_gens [swap 0 1 * swap 2 3, swap 1 2 * swap 0 3] ?_ ?_ ?_ ?_
    ⟨_, List.Mem.head _, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact sign_swap_mul_swap (by decide) (by decide)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide
  · intro s hs t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact mem_closure_list (t := swap 1 2 * swap 0 3) (by decide)
        (List.Mem.tail _ (List.Mem.head _))
    · rw [show swap (0 : Fin 4) 2 * swap 0 1 * (swap 1 2 * swap 0 3) * (swap 0 2 * swap 0 1)⁻¹ =
        (swap 0 1 * swap 2 3) * (swap 1 2 * swap 0 3) by decide]
      exact mul_mem mem_closure_one mem_closure_two

theorem altWit_m6 : AltWit 2 (swap (0 : Fin 6) 2 * swap 0 1 * (swap 3 5 * swap 3 4)) := by
  refine altWit_of_gens [swap 0 3 * swap 1 4, swap 1 4 * swap 2 5] ?_ ?_ ?_ ?_
    ⟨_, List.Mem.head _, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact sign_swap_mul_swap (by decide) (by decide)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide
  · intro s hs t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact mem_closure_list (t := swap 1 4 * swap 2 5) (by decide)
        (List.Mem.tail _ (List.Mem.head _))
    · rw [show swap (0 : Fin 6) 2 * swap 0 1 * (swap 3 5 * swap 3 4) * (swap 1 4 * swap 2 5) *
          (swap 0 2 * swap 0 1 * (swap 3 5 * swap 3 4))⁻¹ =
        (swap 0 3 * swap 1 4) * (swap 1 4 * swap 2 5) by decide]
      exact mul_mem mem_closure_one mem_closure_two

theorem altWit_m9 :
    AltWit 2 (swap (0 : Fin 9) 2 * swap 0 1 * (swap 3 5 * swap 3 4) * (swap 6 8 * swap 6 7)) := by
  refine altWit_of_gens [swap 0 3 * swap 1 4, swap 1 4 * swap 2 5] ?_ ?_ ?_ ?_
    ⟨_, List.Mem.head _, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact sign_swap_mul_swap (by decide) (by decide)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide
  · intro s hs t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> decide
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact mem_closure_list (t := swap 1 4 * swap 2 5) (by decide)
        (List.Mem.tail _ (List.Mem.head _))
    · rw [show swap (0 : Fin 9) 2 * swap 0 1 * (swap 3 5 * swap 3 4) * (swap 6 8 * swap 6 7) *
          (swap 1 4 * swap 2 5) *
          (swap 0 2 * swap 0 1 * (swap 3 5 * swap 3 4) * (swap 6 8 * swap 6 7))⁻¹ =
        (swap 0 3 * swap 1 4) * (swap 1 4 * swap 2 5) by decide]
      exact mul_mem mem_closure_one mem_closure_two

abbrev c10 : Perm (Fin 10) :=
  swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1 * (swap 5 9 * swap 5 8 * swap 5 7 * swap 5 6)

theorem altWit_m10 : AltWit 2 (c10) := by
  refine altWit_of_gens [swap 0 5 * swap 1 6, swap 1 6 * swap 2 7, swap 2 7 * swap 3 8,
    swap 3 8 * swap 4 9] ?_ ?_ ?_ ?_
    ⟨_, List.Mem.head _, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> exact sign_swap_mul_swap (by decide) (by decide)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> decide
  · intro s hs t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs ht
    rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;> decide
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact mem_closure_list (t := swap 1 6 * swap 2 7) (by decide)
        (List.Mem.tail _ (List.Mem.head _))
    · exact mem_closure_list (t := swap 2 7 * swap 3 8) (by decide)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · exact mem_closure_list (t := swap 3 8 * swap 4 9) (by decide)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    · rw [show c10 * (swap 3 8 * swap 4 9) * c10⁻¹ = (swap 0 5 * swap 1 6) *
          (swap 1 6 * swap 2 7) * (swap 2 7 * swap 3 8) * (swap 3 8 * swap 4 9) by decide]
      exact mul_mem (mul_mem (mul_mem mem_closure_one mem_closure_two) mem_closure_three)
        mem_closure_four

theorem altWit_of_three {n : ℕ} (hn : 9 ≤ n) {σ : Perm (Fin n)} (hσ : orderOf σ = 3)
    (hs : σ.support.card ≤ 9) : AltWit 2 σ := by
  obtain ⟨m, hm⟩ := cycleType_prime_order (σ := σ) (by rw [hσ]; exact Nat.prime_three)
  rw [hσ] at hm
  have hsc : σ.support.card = (m + 1) * 3 := by
    rw [← sum_cycleType, hm, Multiset.sum_replicate, smul_eq_mul]
  have hm2 : m ≤ 2 := by omega
  interval_cases m
  · exact altWit_m4.of_cycleType (by omega) (cycleType_eq_of_prime Nat.prime_three hσ
      (orderOf_eq_prime (by decide) (by decide)) (by rw [hsc]; decide))
  · exact altWit_m6.of_cycleType (by omega) (cycleType_eq_of_prime Nat.prime_three hσ
      (orderOf_eq_prime (by decide) (by decide)) (by rw [hsc]; decide))
  · exact altWit_m9.of_cycleType hn (cycleType_eq_of_prime Nat.prime_three hσ
      (orderOf_eq_prime (by decide) (by decide)) (by rw [hsc]; decide))

set_option maxRecDepth 4000 in
theorem altWit_of_five {n : ℕ} (hn : 10 ≤ n) {σ : Perm (Fin n)} (hσ : orderOf σ = 5)
    (hs : σ.support.card = 10) : AltWit 2 σ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact altWit_m10.of_cycleType hn (cycleType_eq_of_prime (by norm_num) hσ
    (orderOf_eq_prime (by decide) (by decide)) (by rw [hs]; decide))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT.FinAltW
