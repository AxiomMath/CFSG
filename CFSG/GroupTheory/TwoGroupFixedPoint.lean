module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

theorem exists_nontrivial_fixed_point_of_isPGroup_two
    {G V : Type} [Group G] [Group V] [MulDistribMulAction G V]
    [Finite G] [Finite V] (hG : IsPGroup 2 G) (hV : IsPGroup 2 V) (h : Nontrivial V) :
    ∃ v : V, v ≠ 1 ∧ ∀ g : G, g • v = v := by
  have hdvd : 2 ∣ Nat.card V := by
    obtain ⟨n, hn, hcard⟩ := hV.nontrivial_iff_card.mp h
    exact hcard.symm ▸ dvd_pow_self 2 (ne_of_gt hn)
  have h1 : (1 : V) ∈ MulAction.fixedPoints G V := by
    rw [MulAction.mem_fixedPoints]
    exact fun g => smul_one g
  obtain ⟨v, hv, hvne⟩ :=
    hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := V) hdvd h1
  exact ⟨v, Ne.symm hvne, fun g => MulAction.mem_fixedPoints.mp hv g⟩

end CFSG
