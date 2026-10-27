module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Thompson

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open CFSG.EvenSporadicStandard.TwoHS

theorem fzb_power_transfer {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {T M : Subgroup G} (hT : FzSylow T) (hMT : M ≤ T)
    (hM : M.relIndex T = 2) {q : G} (hqT : q ∈ T) (hqM : q ∉ M) (hq : q ^ 4 = 1) :
    (∃ a : G, a⁻¹ * q * a ∈ M) ∨ ∃ a : G, a⁻¹ * q ^ 2 * a ∈ T ∧ a⁻¹ * q ^ 2 * a ∉ M := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine false_of_thompson_pow hnab hT.1 hT.2 hMT hM hqT hqM ?_ h1
  intro g k hg
  have hk : q ^ (2 * k) = 1 ∨ q ^ (2 * k) = q ^ 2 := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      have : 2 * (m + m) = 4 * m := by ring
      rw [this, pow_mul, hq, one_pow]
    · right
      have : 2 * (2 * m + 1) = 4 * m + 2 := by ring
      rw [this, pow_add, pow_mul, hq, one_pow, one_mul]
  rcases hk with hk | hk
  · rw [hk]
    simpa using M.one_mem
  · rw [hk] at hg ⊢
    exact h2 g hg

end CFSG.OddStandard.SmallF3.FritzII
