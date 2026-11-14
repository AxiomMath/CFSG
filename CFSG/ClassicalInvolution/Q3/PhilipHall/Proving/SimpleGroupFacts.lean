module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Proving

variable {G : Type*} [Group G]

theorem simple_index_ne_two [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (H : Subgroup G) : H.index ≠ 2 := by
  intro h
  have hN : H.Normal := Subgroup.normal_of_index_eq_two h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with rfl | rfl
  · rw [Subgroup.index_bot] at h
    obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp h
    have hmem : ∀ x : G, x = 1 ∨ x = a := by
      intro x
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (huniq x hx)
    obtain ⟨p, q, hpq⟩ := hnab
    rcases hmem p with rfl | rfl <;> rcases hmem q with rfl | rfl <;> simp_all
  · rw [Subgroup.index_top] at h
    omega

theorem simple_center_eq_bot [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem simple_odd_normal_eq_bot [IsSimpleGroup G] (N : Subgroup G) [N.Normal]
    (hnot : ¬ Odd (Nat.card G)) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · rw [h, Subgroup.card_top] at hodd
    exact absurd hodd hnot

end CFSG.ClassicalInvolution.Q3.PhilipHall.Proving

end
