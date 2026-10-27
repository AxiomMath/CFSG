module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

theorem pSubgroup_le_of_not_dvd_index {X : Type} [Group X] [Finite X] {A D : Subgroup X} {p : Nat}
    (hp : p.Prime) (hAn : A.Normal) (hA : ¬ p ∣ A.index) (hD : IsPGroup p D) : D ≤ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : A.Normal := hAn
  let f : D →* X ⧸ A := (QuotientGroup.mk' A).comp D.subtype
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hdvdD : Nat.card f.range ∣ p ^ k := hk ▸ Subgroup.card_range_dvd f
  have hdvdI : Nat.card f.range ∣ A.index := by
    simpa [Subgroup.index_eq_card] using f.range.card_subgroup_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvdD
  have hj0 : j = 0 := by
    by_contra hne
    have hp_dvd : p ∣ Nat.card f.range := by
      rw [hj]
      exact dvd_pow_self p hne
    exact hA (hp_dvd.trans hdvdI)
  have hbot : f.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_card, hj, hj0, pow_zero]
  have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp hbot
  intro d hd
  have hfd : f ⟨d, hd⟩ = 1 := by simpa [hf]
  have hdA : (d : X ⧸ A) = 1 := by simpa [f] using hfd
  exact (QuotientGroup.eq_one_iff d).mp hdA

end CFSG

end
