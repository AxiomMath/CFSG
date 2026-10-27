module

public import CFSG.LinearAlgebra.LinearGroups.OddPStableActionsSupport
public import CFSG.LinearAlgebra.LinearGroups.QuadraticPCoreImages

public section

namespace CFSG.LinearGroups

open CFSG.GroupTheory

universe u

theorem dihedral_subgroup_actions_are_odd_p_stable {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {n : ℕ} (hn : 2 ≤ n)
    (hS : Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup G))) (H : Subgroup G)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (P : Type u) [Group P] [Finite P]
    (hP : IsPGroup p P) (ρ : H →* MulAut P) : IsPStableAction p ρ := by
  have : Fact p.Prime := ⟨hp⟩
  exact isPStableAction_of_quadratic_images H
    (fun τ => dihedral_subgroup_quadratic_linear_image_in_p_core S hn hS H hp hodd τ) P hP ρ

theorem cyclic_unique_involution_two_sections_have_stable_odd_prime_actions {G : Type*}
    [Group G] [Finite G]
    (hsec : ∀ D : Subgroup G, IsPGroup 2 D → ∀ (E : Subgroup D) [E.Normal],
      (∀ u v : D ⧸ E, orderOf u = 2 → orderOf v = 2 → u = v) → IsCyclic (D ⧸ E))
    (H : Subgroup G) {p : ℕ} (hp : p.Prime) (hodd : Odd p) (P : Type u) [Group P] [Finite P]
    (hP : IsPGroup p P) (ρ : H →* MulAut P) : IsPStableAction p ρ := by
  have : Fact p.Prime := ⟨hp⟩
  exact isPStableAction_of_quadratic_images H
    (fun τ => cyclic_unique_involution_two_sections_give_quadratic_p_core_images hsec H hp hodd τ)
    P hP ρ

end CFSG.LinearGroups
