module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

theorem not_two_pow_nineteen_dvd_half_factorial_23 : ¬ 2 ^ 19 ∣ Nat.factorial 23 / 2 := by
  decide

theorem two_pow_twentyone_dvd_half_factorial_24 : 2 ^ 21 ∣ Nat.factorial 24 / 2 := by
  decide

theorem ds81Lemma210_alt {Y : Type} [Group Y] {n : ℕ} (hn : 5 ≤ n)
    (θ : Y ≃* alternatingGroup (Fin n)) (h19 : 2 ^ 19 ∣ Nat.card Y)
    (h21 : ¬ 2 ^ 21 ∣ Nat.card Y) : False := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  have hY : Nat.card Y = n.factorial / 2 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  rw [hY] at h19 h21
  by_cases hle : n ≤ 23
  · have hdvd : n.factorial / 2 ∣ Nat.factorial 23 / 2 :=
      (Nat.div_dvd_div_iff_right h2 (Nat.dvd_factorial (by norm_num) (by omega))).2
        (Nat.factorial_dvd_factorial hle)
    exact not_two_pow_nineteen_dvd_half_factorial_23 (h19.trans hdvd)
  · have hdvd : Nat.factorial 24 / 2 ∣ n.factorial / 2 :=
      (Nat.div_dvd_div_iff_right (Nat.dvd_factorial (by norm_num) (by norm_num)) h2).2
        (Nat.factorial_dvd_factorial (by omega))
    exact h21 (two_pow_twentyone_dvd_half_factorial_24.trans hdvd)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
