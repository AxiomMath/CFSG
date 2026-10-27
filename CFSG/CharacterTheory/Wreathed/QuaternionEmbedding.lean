module

public import CFSG.CharacterTheory.Wreathed.BaseAndDerived

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

theorem half_modulus_add_self (h : ℕ) :
    (h : ZMod (2 * h)) + h = 0 := by
  rw [← Nat.cast_add, ← two_mul, ZMod.natCast_self]

theorem half_modulus_neg (h : ℕ) : -(h : ZMod (2 * h)) = h := by
  have hs := half_modulus_add_self h
  linear_combination -hs

@[expose] def quaternionEmbedding (h : ℕ) : QuaternionGroup h →* Wreath (2 * h) where
  toFun
    | .a i => element (2 * h) i (-i) 0
    | .xa i => element (2 * h) (h - i) i 1
  map_one' := by
    change element (2 * h) 0 (-0) 0 = 1
    rw [neg_zero, element_zero]
  map_mul' g k := by
    cases g with
    | a i =>
      cases k with
      | a j =>
        change element (2 * h) (i + j) (-(i + j)) 0 = _
        rw [element_base_mul]
        congr 1
        abel
      | xa j =>
        change element (2 * h) (h - (j - i)) (j - i) 1 = _
        rw [element_base_mul]
        congr 1 <;> abel
    | xa i =>
      cases k with
      | a j =>
        change element (2 * h) (h - (i + j)) (i + j) 1 = _
        rw [element_swap_mul, add_zero]
        congr 1
        abel
      | xa j =>
        change element (2 * h) (h + j - i) (-(h + j - i)) 0 = _
        rw [element_swap_mul, show (1 + 1 : ZMod 2) = 0 by decide]
        rw [element_eq_iff]
        refine ⟨?_, ?_, rfl⟩
        · abel
        · have hs := half_modulus_add_self h
          linear_combination -hs

theorem quaternionEmbedding_injective (h : ℕ) : Function.Injective (quaternionEmbedding h) := by
  intro g k heq
  cases g with
  | a i =>
    cases k with
    | a j =>
      change element (2 * h) i (-i) 0 = element (2 * h) j (-j) 0 at heq
      have hij := ((element_eq_iff _ _ _ _ _ _ _).mp heq).1
      rw [hij]
    | xa j =>
      change element (2 * h) i (-i) 0 = element (2 * h) (h - j) j 1 at heq
      have hbad := ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.2
      exact False.elim (zero_ne_one hbad)
  | xa i =>
    cases k with
    | a j =>
      change element (2 * h) (h - i) i 1 = element (2 * h) j (-j) 0 at heq
      have hbad := ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.2
      exact False.elim (one_ne_zero hbad)
    | xa j =>
      change element (2 * h) (h - i) i 1 = element (2 * h) (h - j) j 1 at heq
      have hij := ((element_eq_iff _ _ _ _ _ _ _).mp heq).2.1
      rw [hij]

@[expose] def quaternionSubgroup (h : ℕ) : Subgroup (Wreath (2 * h)) :=
  (quaternionEmbedding h).range

@[expose] def quaternionRangeEquiv (h : ℕ) : QuaternionGroup h ≃* quaternionSubgroup h :=
  MonoidHom.ofInjective (quaternionEmbedding_injective h)

theorem card_quaternionSubgroup (h : ℕ) (hh : 0 < h) : Nat.card (quaternionSubgroup h) = 4 * h := by
  let : NeZero h := ⟨by omega⟩
  rw [← Nat.card_congr (quaternionRangeEquiv h).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem quaternion_range_eq_generated (h : ℕ) :
    quaternionSubgroup h = Subgroup.closure
      {element (2 * h) 1 (-1) 0, element (2 * h) h 0 1} := by
  apply le_antisymm
  · rintro g ⟨a, rfl⟩
    let H := Subgroup.closure {element (2 * h) 1 (-1) 0, element (2 * h) h 0 1}
    have hr : element (2 * h) 1 (-1) 0 ∈ H := Subgroup.subset_closure (by simp)
    have hd : element (2 * h) h 0 1 ∈ H := Subgroup.subset_closure (by simp)
    have hrot (i : ZMod (2 * h)) : element (2 * h) i (-i) 0 ∈ H := by
      have himg : element (2 * h) i (-i) 0 ∈ (antiDiagonalHom (2 * h)).range :=
        ⟨Multiplicative.ofAdd i, rfl⟩
      rw [antiDiagonal_range_eq_zpowers] at himg
      exact Subgroup.zpowers_le_of_mem hr himg
    cases a with
    | a i => exact hrot i
    | xa i =>
      have hp := H.mul_mem hd (hrot i)
      rw [element_swap_mul, add_zero] at hp
      change element (2 * h) (h - i) i 1 ∈ H
      simpa only [sub_eq_add_neg, zero_add] using hp
  · rw [Subgroup.closure_le]
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg1 | hg2
    · rw [hg1]
      exact ⟨QuaternionGroup.a 1, rfl⟩
    · have heq := Set.mem_singleton_iff.mp hg2
      rw [heq]
      refine ⟨QuaternionGroup.xa 0, ?_⟩
      change element (2 * h) (h - 0) 0 1 = element (2 * h) h 0 1
      rw [sub_zero]

end CFSG.Wreathed
