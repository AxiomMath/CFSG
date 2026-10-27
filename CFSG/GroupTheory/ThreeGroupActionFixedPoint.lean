module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

theorem exists_nontrivial_fixed_point_of_isPGroup_three
    {Y B : Type*} [Group Y] [Finite Y] [Group B] [Finite B]
    [MulDistribMulAction Y B] (hY : IsPGroup 3 Y) (hB : IsPGroup 3 B) (hBnt : Nontrivial B) :
    ∃ x : B, x ≠ 1 ∧ ∀ y : Y, y • x = x := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card B := by
    obtain ⟨n, hn, hcard⟩ := hB.nontrivial_iff_card.mp hBnt
    exact hcard.symm ▸ dvd_pow_self 3 (ne_of_gt hn)
  have h1 : (1 : B) ∈ MulAction.fixedPoints Y B := by
    rw [MulAction.mem_fixedPoints]
    exact fun y => smul_one y
  obtain ⟨x, hx, hxne⟩ :=
    hY.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := B) hdvd h1
  exact ⟨x, Ne.symm hxne, fun y => MulAction.mem_fixedPoints.mp hx y⟩

end CFSG
