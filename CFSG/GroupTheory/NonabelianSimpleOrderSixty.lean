module

public import CFSG.GroupTheory.SmallOrderNotSimple
public import CFSG.GroupTheory.SylowCountArithmeticBelowSixty

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem nonabelian_simple_order_at_least_sixty [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ x y : G, x * y ≠ y * x) : 60 ≤ Nat.card G := by
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ Nat.card G := by
    have : Nontrivial G := hs.toNontrivial
    exact Finite.one_lt_card
  have hnot : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ → False := by
    intro N hN h1 h2
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs N hN with h | h
    · exact h1 h
    · exact h2 h
  rcases sylow_count_arithmetic_below_sixty (Nat.card G) h2 hlt
      (fun p a b hp hpG ha hpb hab => by
        obtain ⟨hdvd, hmod, h5⟩ := nonabelian_simple_Sylow_count_minimum hs hna hp hpG ha hpb hab
        exact ⟨Nat.card (Sylow p G), h5, hdvd, hmod⟩) with h30 | h56
  · obtain ⟨N, hN, h1, h2⟩ := order_thirty_not_simple h30
    exact hnot N hN h1 h2
  · obtain ⟨N, hN, h1, h2⟩ := order_fifty_six_not_simple h56
    exact hnot N hN h1 h2

end CFSG.GroupTheory
