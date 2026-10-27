module

public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Assembly.LowTwoRank

variable (n : ℕ) (K : Type) [Field K]

theorem infinite_or_four_le_card_of_finset {K : Type*} (h : ∃ s : Finset K, s.card = 4) :
    Infinite K ∨ 4 ≤ Nat.card K := by
  rcases finite_or_infinite K with hfin | hinf
  · obtain ⟨s, hs⟩ := h
    have : Fintype K := Fintype.ofFinite K
    refine Or.inr ?_
    rw [Nat.card_eq_fintype_card, ← hs]
    exact Finset.card_le_univ s
  · exact Or.inl hinf

theorem isPerfect_statedSp (h : (∃ s : Finset K, s.card = 4) ∨ (Nat.card K = 3 ∧ 2 ≤ n) ∨
    (Nat.card K = 2 ∧ 3 ≤ n)) : Group.IsPerfect (StatedSp n K) := by
  have h' : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ n) ∨
      (Nat.card K = 2 ∧ 3 ≤ n) := by
    rcases h with h4 | h
    · exact Or.inl (infinite_or_four_le_card_of_finset h4)
    · exact Or.inr h
  have : Group.IsPerfect (TauCeti.GLSymplecticFin n K) := isPerfect_GLSymplecticFin K n h'
  let e : TauCeti.GLSymplecticFin n K ≃* StatedSp n K :=
    (TauCeti.GLSymplecticFin.mulEquivGLSymplectic n K).trans
      (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := n) (K := K)).symm)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem isPerfect_statedSp_quotient (h : (∃ s : Finset K, s.card = 4) ∨
    (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) (N : Subgroup (StatedSp n K))
    [N.Normal] : Group.IsPerfect (StatedSp n K ⧸ N) := by
  have := isPerfect_statedSp n K h
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

theorem symplectic_projective_perfect (h : (∃ s : Finset K, s.card = 4) ∨
    (Nat.card K = 3 ∧ 2 ≤ n) ∨ (Nat.card K = 2 ∧ 3 ≤ n)) :
    Group.IsPerfect (StatedProj (StatedSp n K)) :=
  isPerfect_statedSp_quotient n K h _

end CFSG.ClassicalGroups.Symplectic
