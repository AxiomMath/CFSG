module

public import CFSG.LocalAnalysis.Mason73.Fusion33

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

variable {n : ℕ}

@[expose] def V1 : Subgroup Fin81.R0 where
  carrier := {π | (π : Perm (Fin 4)) = 1 ∨ (π : Perm (Fin 4)) = swap 0 1 ∨
    (π : Perm (Fin 4)) = swap 2 3 ∨ (π : Perm (Fin 4)) = swap 0 1 * swap 2 3}
  mul_mem' := by
    intro a b ha hb
    have key : ∀ π σ : Perm (Fin 4),
        (π = 1 ∨ π = swap 0 1 ∨ π = swap 2 3 ∨ π = swap 0 1 * swap 2 3) →
        (σ = 1 ∨ σ = swap 0 1 ∨ σ = swap 2 3 ∨ σ = swap 0 1 * swap 2 3) →
        (π * σ = 1 ∨ π * σ = swap 0 1 ∨ π * σ = swap 2 3 ∨ π * σ = swap 0 1 * swap 2 3) := by
      decide
    exact key _ _ ha hb
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    have key : ∀ π : Perm (Fin 4),
        (π = 1 ∨ π = swap 0 1 ∨ π = swap 2 3 ∨ π = swap 0 1 * swap 2 3) →
        (π⁻¹ = 1 ∨ π⁻¹ = swap 0 1 ∨ π⁻¹ = swap 2 3 ∨ π⁻¹ = swap 0 1 * swap 2 3) := by
      decide
    exact key _ ha

instance : DecidablePred (· ∈ V1) := fun π =>
  inferInstanceAs (Decidable ((π : Perm (Fin 4)) = 1 ∨ (π : Perm (Fin 4)) = swap 0 1 ∨
    (π : Perm (Fin 4)) = swap 2 3 ∨ (π : Perm (Fin 4)) = swap 0 1 * swap 2 3))

theorem card_V1 : Nat.card V1 = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem index_V1 : V1.index = 2 := by
  have h := Subgroup.card_mul_index V1
  rw [card_V1, Fin81.card_R0] at h
  omega

abbrev Q1T (n : ℕ) : Subgroup (L4Model n) := V1.comap piT

theorem index_Q1T : (Q1T n).index = 2 := by
  rw [Subgroup.index_comap_of_surjective _ piT_surjective, index_V1]

theorem A_le_Q1T : A n ≤ Q1T n := fun x hx => by
  rw [Subgroup.mem_comap, mem_A_iff.1 hx]
  exact one_mem _

theorem tT_not_mem_Q1T (hn : 1 ≤ n) : tT (n := n) hn ∉ Q1T n := by
  have key : ¬ ((swap 0 2 * swap 1 3 : Perm (Fin 4)) = 1 ∨
      (swap 0 2 * swap 1 3 : Perm (Fin 4)) = swap 0 1 ∨
      (swap 0 2 * swap 1 3 : Perm (Fin 4)) = swap 2 3 ∨
      (swap 0 2 * swap 1 3 : Perm (Fin 4)) = swap 0 1 * swap 2 3) := by
    decide
  exact key

theorem orderOf_tT (hn : 2 ≤ n) : orderOf (tT (n := n) (by omega)) = 2 := by
  refine orderOf_eq_prime (by rw [pow_two]; exact tT_mul_self hn) fun h => ?_
  exact tT_not_mem_A (n := n) (by omega) (h ▸ one_mem _)

end CFSG.LocalAnalysis.Mason73
