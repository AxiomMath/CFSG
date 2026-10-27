module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace MuTab

open Equiv in
@[expose] def wylPerm : Fin 4 → Equiv.Perm (Fin 8) :=
  ![swap 0 1 * swap 4 5, swap 1 2 * swap 5 6, swap 2 3 * swap 6 7, swap 2 7 * swap 6 3]

theorem wylPerm_liftable : coxeterD4.IsLiftable wylPerm := by
  unfold CoxeterMatrix.IsLiftable
  decide

theorem wylPerm_powers :
    ∀ k : ℕ, 1 ≤ k → k ≤ 4 → (wylPerm 1 * wylPerm 0 * wylPerm 2 * wylPerm 3) ^ k ≠ 1 := by
  decide

theorem exists_wyl_element : ∃ g : coxeterD4.Group, g ≠ 1 ∧ g ^ 2 ≠ 1 ∧ g ^ 3 ≠ 1 ∧ g ^ 4 ≠ 1 := by
  let cs := coxeterD4.toCoxeterSystem
  let φ : coxeterD4.Group →* Equiv.Perm (Fin 8) := cs.lift ⟨wylPerm, wylPerm_liftable⟩
  have hφ : ∀ i, φ (cs.simple i) = wylPerm i := fun i => cs.lift_apply_simple wylPerm_liftable i
  let g : coxeterD4.Group := cs.simple 1 * cs.simple 0 * cs.simple 2 * cs.simple 3
  have hg : φ g = wylPerm 1 * wylPerm 0 * wylPerm 2 * wylPerm 3 := by
    simp only [g, map_mul, hφ]
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → g ^ k ≠ 1 := fun k h1 h2 h => by
    have := congrArg φ h
    rw [map_pow, hg, map_one] at this
    exact wylPerm_powers k h1 h2 this
  exact ⟨g, by simpa using key 1 le_rfl (by norm_num), key 2 (by norm_num) (by norm_num),
    key 3 (by norm_num) (by norm_num), key 4 (by norm_num) le_rfl⟩

theorem small_elements_z2 :
    ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  decide

theorem small_elements_perm3 :
    ∀ x : Equiv.Perm (Fin 3), x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  decide

theorem small_elements_klein :
    ∀ x : Multiplicative (ZMod 2 × ZMod 2), x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  decide

theorem small_elements_perm4 :
    ∀ x : Equiv.Perm (Fin 4), x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1 := by
  decide

theorem not_wyl_equiv {X : Type*} [Group X]
    (hX : ∀ x : X, x = 1 ∨ x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 4 = 1) :
    ¬ Nonempty (coxeterD4.Group ≃* X) := by
  rintro ⟨e⟩
  obtain ⟨g, h1, h2, h3, h4⟩ := exists_wyl_element
  rcases hX (e g) with h | h | h | h
  · exact h1 (e.injective (by rw [h, map_one]))
  · exact h2 (e.injective (by rw [map_pow, h, map_one]))
  · exact h3 (e.injective (by rw [map_pow, h, map_one]))
  · exact h4 (e.injective (by rw [map_pow, h, map_one]))

theorem not_wyl_equiv_z2 : ¬ Nonempty (coxeterD4.Group ≃* Multiplicative (ZMod 2)) :=
  not_wyl_equiv small_elements_z2

theorem not_wyl_equiv_perm3 : ¬ Nonempty (coxeterD4.Group ≃* Equiv.Perm (Fin 3)) :=
  not_wyl_equiv small_elements_perm3

theorem not_wyl_equiv_klein :
    ¬ Nonempty (coxeterD4.Group ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
  not_wyl_equiv small_elements_klein

theorem not_wyl_equiv_perm4 : ¬ Nonempty (coxeterD4.Group ≃* Equiv.Perm (Fin 4)) :=
  not_wyl_equiv small_elements_perm4

end MuTab

end CFSG.ClassicalInvolution.Asc77
