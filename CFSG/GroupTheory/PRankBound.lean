module

public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_of_not_dvd_pow_succ {H : Subgroup G} {p k : ℕ} (hp : p.Prime)
    (h : ¬ p ^ (k + 1) ∣ Nat.card H) : CFSG.Open.pRank p H ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le (G := G) (H := H) (k := k) hp.one_lt fun E hEH hE => ?_
  have hEp : IsPGroup p ↥E := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx : (x : ↥E) ^ p = 1 := by
      apply Subtype.ext
      exact hE.2 (x : G) x.2
    have hdvd : orderOf (x : ↥E) ∣ p := orderOf_dvd_of_pow_eq_one hx
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [hp', pow_one]⟩
  obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (G := ↥E) hEp
  have hdvd : Nat.card ↥E ∣ Nat.card H := Subgroup.card_dvd_of_le hEH
  rw [hm] at hdvd
  have hmk : m ≤ k := by
    by_contra hlt
    exact h ((pow_dvd_pow p (by omega : k + 1 ≤ m)).trans hdvd)
  rw [hm]
  exact Nat.pow_le_pow_right hp.pos hmk

end CFSG.GroupTheory

end
