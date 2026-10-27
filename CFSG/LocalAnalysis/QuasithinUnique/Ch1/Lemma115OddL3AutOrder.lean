module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg
open scoped MatrixGroups

section Order

variable {F : Type} [Field F] [Finite F]

theorem card_specialLinear_three {p : ℕ} (hF : Nat.card F = p) :
    Nat.card SL(3, F) = p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) := by
  rw [Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv]
  exact CFSG.SectionRank.OddCover.card_statedSL_three_eq_mul hF

theorem exists_odd_mul_card_projectiveSL {p : ℕ} (hF : Nat.card F = p) :
    ∃ z, Odd z ∧ Nat.card (projectiveSL 3 F) * z =
      p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1)) := by
  refine ⟨Nat.card (scalars 3 F), ?_, ?_⟩
  · have hdvd : Nat.card (scalars 3 F) ∣ 3 := by
      rw [scalars_eq_center]
      exact (card_center_specialLinearGroup_dvd (by norm_num) F).trans (Nat.gcd_dvd_left _ _)
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨1, rfl⟩
  · rw [← card_specialLinear_three hF,
      Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars 3 F)]

theorem not_card_dvd_of_sylow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hF : Nat.card F = p)
    (P : Sylow 2 (projectiveSL 3 F)) : ¬ Nat.card P ∣ p * (p ^ 2 - 1) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hmul⟩ := exists_odd_mul_card_projectiveSL hF
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
  have hpn : Nat.card (projectiveSL 3 F) ≠ 0 := Nat.card_pos.ne'
  have hz0 : z ≠ 0 := hz.pos.ne'
  have hP : Nat.card P = 2 ^ padicValNat 2 (Nat.card (projectiveSL 3 F)) := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ Nat.prime_two]
  have ha : 2 ∣ p - 1 := by omega
  have hb : 2 ∣ p + 1 := by omega
  have ha0 : p - 1 ≠ 0 := by omega
  have hb0 : p + 1 ≠ 0 := by omega
  have hc : ¬ 2 ∣ p ^ 2 + p + 1 := by
    have : (p ^ 2 + p + 1) % 2 = 1 := by
      have h1 : p ^ 2 % 2 = 1 := by simp [Nat.pow_mod, hpodd]
      omega
    omega
  have hc0 : p ^ 2 + p + 1 ≠ 0 := by omega
  have hp0 : p ≠ 0 := by omega
  have hpn2 : ¬ 2 ∣ p := by omega
  have hab : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    have h1 : 1 ≤ p := by omega
    have h2 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  rw [hP, hab] at hdvd
  have hab0 : (p - 1) * (p + 1) ≠ 0 := mul_ne_zero ha0 hb0
  have hac0 : (p - 1) * (p ^ 2 + p + 1) ≠ 0 := mul_ne_zero ha0 hc0
  have hp30 : p ^ 3 ≠ 0 := pow_ne_zero 3 hp0
  have hv1 : padicValNat 2 (Nat.card (projectiveSL 3 F)) ≤
      padicValNat 2 (p * ((p - 1) * (p + 1))) :=
    (padicValNat_dvd_iff_le (mul_ne_zero hp0 hab0)).1 hdvd
  have hvz : padicValNat 2 z = 0 := padicValNat.eq_zero_of_not_dvd (by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.2 hz)
  have hv2 : padicValNat 2 (Nat.card (projectiveSL 3 F)) =
      padicValNat 2 (p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1))) := by
    rw [← hmul, padicValNat.mul hpn hz0, hvz, add_zero]
  have hvp : padicValNat 2 p = 0 := padicValNat.eq_zero_of_not_dvd hpn2
  have hvc : padicValNat 2 (p ^ 2 + p + 1) = 0 := padicValNat.eq_zero_of_not_dvd hc
  have hva : 1 ≤ padicValNat 2 (p - 1) := one_le_padicValNat_of_dvd ha0 ha
  have hM : padicValNat 2 (p ^ 3 * ((p - 1) * (p + 1)) * ((p - 1) * (p ^ 2 + p + 1))) =
      3 * 0 + (padicValNat 2 (p - 1) + padicValNat 2 (p + 1)) +
        (padicValNat 2 (p - 1) + 0) := by
    rw [padicValNat.mul (mul_ne_zero hp30 hab0) hac0, padicValNat.mul hp30 hab0,
      padicValNat.mul ha0 hb0, padicValNat.mul ha0 hc0, padicValNat.pow p 3, hvp, hvc]
  have hN : padicValNat 2 (p * ((p - 1) * (p + 1))) =
      padicValNat 2 (p - 1) + padicValNat 2 (p + 1) := by
    rw [padicValNat.mul hp0 hab0, padicValNat.mul ha0 hb0, hvp, zero_add]
  rw [hv2, hM, hN] at hv1
  omega

end Order

end CFSG.QuasithinUnique.Ch1
