module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossArith
public import CFSG.GH74.Generic.Context
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

private theorem eq_three_of_pow_three_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 3 ∣ Nat.factorial 11) : p = 3 := by
  have hp11 : p ≤ 11 :=
    (hp.dvd_factorial).1 ((dvd_pow_self p (by norm_num)).trans h)
  have hp1 := hp.two_le
  interval_cases p
  · exact absurd rfl hp2
  · rfl
  · exact absurd hp (by norm_num)
  · exfalso; revert h; decide
  · exact absurd hp (by norm_num)
  · exfalso; revert h; decide
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exfalso; revert h; decide

private theorem le_one_of_three_pow_dvd_factorial_eleven {f : ℕ}
    (h : 3 ^ (3 * f) ∣ Nat.factorial 11) : f ≤ 1 := by
  by_contra hne
  have h6 : 3 ^ 6 ∣ Nat.factorial 11 := (pow_dvd_pow 3 (by omega)).trans h
  revert h6
  decide

private theorem pow_three_dvd_psl3Order {q : ℕ} (hq : 1 ≤ q) : q ^ 3 ∣ psl3Order q := by
  have hdvd : q - 1 ∣ q ^ 3 - 1 := Nat.sub_one_dvd_pow_sub_one q 3
  have hg : Nat.gcd 3 (q - 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
    ((Nat.gcd_dvd_right 3 (q - 1)).trans hdvd).trans (dvd_mul_left _ _)
  have hcop : Nat.Coprime (q ^ 3) (Nat.gcd 3 (q - 1)) := by
    refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (q - 1)) ?_)
    obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    simp
  have hmul : psl3Order q * Nat.gcd 3 (q - 1) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
    Nat.div_mul_cancel hg
  have hdiv : q ^ 3 ∣ psl3Order q * Nat.gcd 3 (q - 1) := by
    rw [hmul]
    exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  exact hcop.dvd_of_dvd_mul_right hdiv

theorem not_card_dvd_factorial_of_FL3 {Y : Type} [Group Y] [Finite Y] (hY : FL3 Y) :
    ¬ Nat.card Y ∣ Nat.factorial 11 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hLie
  have hcard : Nat.card Y = psl3Order (p ^ f) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
    exact (psl3Order_eq_linearModel _).symm
  have hq3 : (p ^ f) ^ 3 ∣ Nat.card Y :=
    hcard ▸ pow_three_dvd_psl3Order (Nat.one_le_pow _ _ hp.pos)
  intro h
  have h1 : p ^ (3 * f) ∣ Nat.factorial 11 := by
    refine dvd_trans ?_ h
    rw [← pow_mul, mul_comm] at hq3
    exact hq3
  have hp3 : p = 3 :=
    eq_three_of_pow_three_dvd_factorial_eleven hp hp2
      ((pow_dvd_pow p (by omega : 3 ≤ 3 * f)).trans h1)
  subst hp3
  have hf1 : f = 1 := le_antisymm (le_one_of_three_pow_dvd_factorial_eleven h1) hf
  subst hf1
  rw [hcard] at h
  revert h
  decide

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
