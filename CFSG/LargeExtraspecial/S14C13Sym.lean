module

public import CFSG.LargeExtraspecial.S14C10Sym3

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup

theorem perm_three_involution :
    ∀ a : Equiv.Perm (Fin 3), a * a = 1 → a ≠ 1 →
      a = Equiv.swap 0 1 ∨ a = Equiv.swap 0 2 ∨ a = Equiv.swap 1 2 := by
  decide

theorem exists_conj_swap_pair (a b : Equiv.Perm (Fin 3)) (ha : a * a = 1) (ha1 : a ≠ 1)
    (hb : b * b = 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 3), σ * Equiv.swap 0 1 * σ⁻¹ = a ∧ σ * Equiv.swap 1 2 * σ⁻¹ = b := by
  rcases perm_three_involution a ha ha1 with rfl | rfl | rfl <;>
    rcases perm_three_involution b hb hb1 with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hab
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 1 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1 * Equiv.swap 0 2, by decide, by decide⟩
    | exact ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩

theorem fst_eq_one_of_perfect {A P : Type*} [Group A] [Group P]
    (φ : A →* Equiv.Perm (Fin 3) × P) {K : Subgroup A} (hK : ⁅K, K⁆ = K) :
    ∀ k ∈ K, (φ k).1 = 1 := by
  have hKψ : K.map ((MonoidHom.fst (Equiv.Perm (Fin 3)) P).comp φ) = ⊥ := by
    refine eq_bot_of_perfect_perm_three ?_
    rw [← map_commutator, hK]
  intro k hk
  have : ((MonoidHom.fst (Equiv.Perm (Fin 3)) P).comp φ) k ∈
      K.map ((MonoidHom.fst (Equiv.Perm (Fin 3)) P).comp φ) := ⟨k, hk, rfl⟩
  rw [hKψ, mem_bot] at this
  exact this

end CFSG.LargeExtraspecial.S14
