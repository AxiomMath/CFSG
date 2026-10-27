module

public import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.GroupTheory

theorem groups_order_below_sixty_solvable {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G < 60) : Group.IsSolvable G := by
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    subst hn
    by_cases hnt : Nontrivial G
    · by_cases hN : ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤
      · obtain ⟨N, hNn, hNb, hNt⟩ := hN
        have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup N
        have hN1 : 1 < Nat.card N := by
          rw [Subgroup.one_lt_card_iff_ne_bot]
          exact hNb
        have hQ1 : 1 < Nat.card (G ⧸ N) := by
          exact Subgroup.one_lt_index_of_ne_top hNt
        have hpos : 0 < Nat.card G := Nat.card_pos
        have hNlt : Nat.card N < Nat.card G := by
          rw [hcard]
          exact lt_mul_left (by omega) hQ1
        have hQlt : Nat.card (G ⧸ N) < Nat.card G := by
          rw [hcard]
          exact lt_mul_right (by omega) hN1
        have : Group.IsSolvable N := ih _ hNlt (by omega) rfl
        have : Group.IsSolvable (G ⧸ N) := ih _ hQlt (by omega) rfl
        exact Group.isSolvable_of_subgroup_quotient N
      · push Not at hN
        have hs : IsSimpleGroup G := ⟨fun N hNn => by
          by_contra h
          push Not at h
          exact h.2 (hN N hNn h.1)⟩
        by_cases hcomm : ∀ x y : G, x * y = y * x
        · exact Group.isSolvable_of_comm hcomm
        · push Not at hcomm
          exact absurd (nonabelian_simple_order_at_least_sixty hs hcomm) (by omega)
    · have : Subsingleton G := not_nontrivial_iff_subsingleton.1 hnt
      infer_instance

end CFSG.GroupTheory
