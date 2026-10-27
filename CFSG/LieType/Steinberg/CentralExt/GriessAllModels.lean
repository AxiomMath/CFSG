module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
public import CFSG.LieType.Steinberg.CentralExt.GriessTwistedE6
public import CFSG.LieType.Steinberg.CentralExt.GriessTriality
public import CFSG.LieType.Steinberg.CentralExt.GriessSuzuki
public import CFSG.LieType.Steinberg.CentralExt.GriessReeF4
public import CFSG.LieType.Steinberg.CentralExt.GriessSmallRee
public import CFSG.LieType.Steinberg.CentralExt.GriessUnitaryOdd
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaSevenThree
import CFSG.Models.Blueprint

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessAll

abbrev GriessRow (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  commutator X = ⊤ ∧
    Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic t n p f × exceptional t n p f)

theorem eq_of_pow_eq_prime {p f q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ^ f = q) :
    p = q ∧ f = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    exact hq.one_lt.ne h
  have hpq : p ∣ q := h ▸ dvd_pow_self p hf
  have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  subst hpq'
  exact ⟨rfl, Nat.pow_right_injective hp.two_le (show p ^ f = p ^ 1 by rw [h, pow_one])⟩

theorem eq_of_pow_eq_four {p f : ℕ} (hp : p.Prime) (h : p ^ f = 4) : p = 2 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at h
    omega
  have hp2 : p ∣ 2 ^ 2 := by rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h]; exact dvd_pow_self p hf
  have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hp2)
  subst hp2'
  exact ⟨rfl, Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [h])⟩

theorem classical_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (h : CFSG.Models.LieModel X t n p f) (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨
      t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    StatedClassicalModel X t n p f :=
  CFSG.Models.LieModel.statedClassicalModel h
    (by rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)


variable {X : Type} [Group X]

theorem griess_all_models_of_remaining
    (hG23 : ∀ (Y : Type) [Group Y], CFSG.Models.LieModel Y .G2 0 3 1 → GriessRow Y .G2 0 3 1)
    (hG24 : ∀ (Y : Type) [Group Y], CFSG.Models.LieModel Y .G2 0 2 2 → GriessRow Y .G2 0 2 2)
    (hF42 : ∀ (Y : Type) [Group Y], CFSG.Models.LieModel Y .F4 0 2 1 → GriessRow Y .F4 0 2 1)
    (h2E62 : ∀ (Y : Type) [Group Y], CFSG.Models.LieModel Y .twistedE6 0 2 1 →
      GriessRow Y .twistedE6 0 2 1)
    (t : StatedLieTag) (n p f : ℕ) (hmodel : CFSG.Models.LieModel X t n p f) :
    GriessRow X t n p f := by
  have hadm := hmodel.1
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  cases t with
  | PSL => exact GriessClassical.psl_row (classical_of_lieModel hmodel (by simp))
  | PSU =>
    have hn : 3 ≤ n := hadm.2.2.1
    by_cases he : Even n
    · by_cases hq : 4 ≤ p ^ f ∨ (p ^ f = 2 ∧ 8 ≤ n) ∨ (p ^ f = 3 ∧ 6 ≤ n)
      · exact GriessClassical.psu_row (classical_of_lieModel hmodel (by simp)) he hq
      · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
        obtain ⟨k, hk⟩ := he
        rcases hq' with h2 | h3
        · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_two h2
          have : n = 4 ∨ n = 6 := by omega
          rcases this with rfl | rfl
          · exact GriessClassical.psu_four_two_row hmodel
          · exact GriessClassical.psu_six_two_row hmodel
        · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_three h3
          have : n = 4 := by omega
          subst this
          exact GriessClassical.psu_four_three_row hmodel
    · exact GriessClassical.psu_odd_row (classical_of_lieModel hmodel (by simp)) he
  | PSp =>
    have hn : 2 ≤ n := hadm.2.2.1
    by_cases hq : 5 ≤ p ^ f ∨ p ^ f = 4 ∨ (p ^ f = 2 ∧ 4 ≤ n) ∨ (p ^ f = 3 ∧ 3 ≤ n)
    · exact GriessClassical.psp_row (classical_of_lieModel hmodel (by simp)) hq
    · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
      rcases hq' with h2 | h3
      · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_two h2
        have hn3 : n = 2 ∨ n = 3 := by omega
        rcases hn3 with rfl | rfl
        · exact absurd rfl hadm.2.2.2
        · exact GriessClassical.psp_three_two_row hmodel
      · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 2 := by omega
        subst this
        exact GriessClassical.psp_four_three_row hmodel
  | POmegaOdd =>
    have hn : 3 ≤ n := hadm.2.2.1
    have hp2 : p ≠ 2 := hadm.2.2.2
    by_cases hq : 5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n)
    · exact GriessClassical.pomegaOdd_row (classical_of_lieModel hmodel (by simp)) hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 ∨ p ^ f = 2 := by omega
      rcases hq' with h3 | h4 | h2
      · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 3 := by omega
        subst this
        exact GriessClassical.pomegaOdd_three_three_row hmodel
      · exact absurd (eq_of_pow_eq_four hp h4).1 hp2
      · exact absurd (eq_of_pow_eq_prime hp Nat.prime_two h2).1 hp2
  | POmegaPlus =>
    have hn : 4 ≤ n := hadm.2.2
    by_cases hq : 3 ≤ p ^ f ∨ (p ^ f = 2 ∧ 5 ≤ n)
    · exact GriessClassical.pomegaPlus_row (classical_of_lieModel hmodel (by simp)) hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_two h2
      have : n = 4 := by omega
      subst this
      exact GriessClassical.pomegaPlus_four_two_row hmodel
  | POmegaMinus => exact GriessClassical.pomegaMinus_row (classical_of_lieModel hmodel (by simp))
  | G2 =>
    obtain ⟨hn0, hq3⟩ := hadm.2.2
    subst hn0
    by_cases hq : 5 ≤ p ^ f
    · exact GriessExceptional.g2_row hmodel hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 := by omega
      rcases hq' with h3 | h4
      · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_three h3
        exact hG23 X hmodel
      · obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_four hp h4
        exact hG24 X hmodel
  | F4 =>
    have hn0 : n = 0 := hadm.2.2
    subst hn0
    by_cases hq : 3 ≤ p ^ f
    · exact GriessExceptional.f4_row hmodel hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_two h2
      exact hF42 X hmodel
  | E6 => exact GriessExceptional.e6_row hmodel
  | E7 => exact GriessExceptional.e7_row hmodel
  | E8 => exact GriessExceptional.e8_row hmodel
  | twistedE6 =>
    have hn0 : n = 0 := hadm.2.2
    subst hn0
    by_cases hq : 3 ≤ p ^ f
    · exact GriessExceptional.twistedE6_row hmodel hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := eq_of_pow_eq_prime hp Nat.prime_two h2
      exact h2E62 X hmodel
  | trialityD4 => exact GriessExceptional.trialityD4_row hmodel
  | twistedB2 => exact GriessExceptional.twistedB2_row hmodel
  | twistedG2 => exact GriessExceptional.twistedG2_row hmodel
  | twistedF4 => exact GriessExceptional.twistedF4_row hmodel
  | Tits => exact GriessExceptional.tits_row hmodel

end CFSG.LieType.Steinberg.CentralExt.GriessAll
