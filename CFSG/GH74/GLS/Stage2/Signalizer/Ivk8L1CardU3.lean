module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU3Card
public import CFSG.GH74.Generic.Context

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.LocalAnalysis.ComponentInitial

private theorem not_pow_six_dvd_factorial_eleven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 6 ∣ Nat.factorial 11 := by
  intro h
  have hp11 : p ≤ 11 :=
    (hp.dvd_factorial).1 ((dvd_pow_self p (by norm_num)).trans h)
  have hp1 := hp.two_le
  interval_cases p
  · exact hp2 rfl
  all_goals (revert h; decide)

private theorem pow_three_dvd_psu3Order (q : ℕ) : q ^ 3 ∣ psu3Order q := by
  have hdvd : q + 1 ∣ q ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  have hg : Nat.gcd 3 (q + 1) ∣ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
    ((Nat.gcd_dvd_right 3 (q + 1)).trans hdvd).trans (dvd_mul_left _ _)
  have hcop : Nat.Coprime (q ^ 3) (Nat.gcd 3 (q + 1)) :=
    Nat.Coprime.pow_left 3
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (q + 1)) (by simp))
  have hmul : psu3Order q * Nat.gcd 3 (q + 1) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) :=
    Nat.div_mul_cancel hg
  have hq : q ^ 3 ∣ psu3Order q * Nat.gcd 3 (q + 1) := by
    rw [hmul]
    exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  exact hcop.dvd_of_dvd_mul_right hq

theorem not_card_sq_dvd_factorial_of_FU3 {Y : Type} [Group Y] [Finite Y] (hY : FU3 Y) :
    ¬ (Nat.card Y) ^ 2 ∣ Nat.factorial 11 := by
  obtain ⟨p, f, hp, hf, hp2, hLie⟩ := hY
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hLie
  have hud : UnitaryFieldData p f F := ⟨hp, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hcard : Nat.card Y = psu3Order (p ^ f) :=
    (Nat.card_congr e.toEquiv).trans (card_statedProj_su3 hud)
  have hq3 : (p ^ f) ^ 3 ∣ Nat.card Y := hcard ▸ pow_three_dvd_psu3Order (p ^ f)
  intro h
  refine not_pow_six_dvd_factorial_eleven hp hp2 (dvd_trans ?_ h)
  calc p ^ 6 ∣ p ^ (6 * f) := pow_dvd_pow p (by omega)
    _ = ((p ^ f) ^ 3) ^ 2 := by ring
    _ ∣ (Nat.card Y) ^ 2 := pow_dvd_pow_of_dvd hq3 2

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L1
