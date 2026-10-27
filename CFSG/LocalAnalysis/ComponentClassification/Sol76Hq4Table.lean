module

public import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo
public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoFour
public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoThree
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

@[expose] def NativeRowsExceptTwistedE6Two : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), CFSG.Blueprint.LieModel X t n p f →
    ¬ (t = .twistedE6 ∧ p ^ f = 2) → GriessAll.GriessRow X t n p f

theorem nativeRowsExceptTwistedE6Two :
    NativeRowsExceptTwistedE6Two := by
  intro X _ t n p f hmodel hne
  have hadm := GriessNative.admissible_of_lieModel hmodel
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  cases t with
  | PSL => exact GriessClassical.psl_row (GriessNative.classical_of_lieModel hmodel (by decide))
  | PSU =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hM := GriessNative.models_lieModel_of_classical hcl
    have hn : 3 ≤ n := hadm.2.2.1
    by_cases he : Even n
    · by_cases hq : 4 ≤ p ^ f ∨ (p ^ f = 2 ∧ 8 ≤ n) ∨ (p ^ f = 3 ∧ 6 ≤ n)
      · exact GriessClassical.psu_row hcl he hq
      · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
        obtain ⟨k, hk⟩ := he
        rcases hq' with h2 | h3
        · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
          have : n = 4 ∨ n = 6 := by omega
          rcases this with rfl | rfl
          · exact GriessClassical.psu_four_two_row hM
          · exact GriessClassical.psu_six_two_row hM
        · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
          have : n = 4 := by omega
          subst this
          exact GriessClassical.psu_four_three_row hM
    · exact GriessClassical.psu_odd_row hcl he
  | PSp =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hM := GriessNative.models_lieModel_of_classical hcl
    have hn : 2 ≤ n := hadm.2.2.1
    by_cases hq : 5 ≤ p ^ f ∨ p ^ f = 4 ∨ (p ^ f = 2 ∧ 4 ≤ n) ∨ (p ^ f = 3 ∧ 3 ≤ n)
    · exact GriessClassical.psp_row hcl hq
    · have hq' : p ^ f = 2 ∨ p ^ f = 3 := by omega
      rcases hq' with h2 | h3
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
        have hn3 : n = 2 ∨ n = 3 := by omega
        rcases hn3 with rfl | rfl
        · exact absurd rfl hadm.2.2.2
        · exact GriessClassical.psp_three_two_row hM
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 2 := by omega
        subst this
        exact GriessClassical.psp_four_three_row hM
  | POmegaOdd =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hM := GriessNative.models_lieModel_of_classical hcl
    have hn : 3 ≤ n := hadm.2.2.1
    have hp2 : p ≠ 2 := hadm.2.2.2
    by_cases hq : 5 ≤ p ^ f ∨ (p ^ f = 3 ∧ 4 ≤ n)
    · exact GriessClassical.pomegaOdd_row hcl hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 ∨ p ^ f = 2 := by omega
      rcases hq' with h3 | h4 | h2
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        have : n = 3 := by omega
        subst this
        exact GriessClassical.pomegaOdd_three_three_row hM
      · exact absurd (GriessAll.eq_of_pow_eq_four hp h4).1 hp2
      · exact absurd (GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2).1 hp2
  | POmegaPlus =>
    have hcl := GriessNative.classical_of_lieModel hmodel (by decide)
    have hM := GriessNative.models_lieModel_of_classical hcl
    have hn : 4 ≤ n := hadm.2.2
    by_cases hq : 3 ≤ p ^ f ∨ (p ^ f = 2 ∧ 5 ≤ n)
    · exact GriessClassical.pomegaPlus_row hcl hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
      have : n = 4 := by omega
      subst this
      exact GriessClassical.pomegaPlus_four_two_row hM
  | POmegaMinus =>
    exact GriessClassical.pomegaMinus_row (GriessNative.classical_of_lieModel hmodel (by decide))
  | G2 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    have hq3 : 3 ≤ p ^ f := hadm.2.2.2
    by_cases hq : 5 ≤ p ^ f
    · exact GriessNative.g2_row hce hq
    · have hq' : p ^ f = 3 ∨ p ^ f = 4 := by omega
      rcases hq' with h3 | h4
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_three h3
        exact GriessExceptional.g2_three_native_row hce
      · obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_four hp h4
        exact GriessExceptional.g2_four_native_row hce
  | F4 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    by_cases hq : 3 ≤ p ^ f
    · exact GriessNative.f4_row hce hq
    · have h2 : p ^ f = 2 := by omega
      obtain ⟨rfl, rfl⟩ := GriessAll.eq_of_pow_eq_prime hp Nat.prime_two h2
      exact GriessExceptional.f4_two_native_row hce
  | E6 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e6_row hce
  | E7 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e7_row hce
  | E8 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.e8_row hce
  | twistedE6 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    by_cases hq : 3 ≤ p ^ f
    · exact GriessNative.twistedE6_row hce hq
    · have h2 : p ^ f = 2 := by omega
      exact absurd ⟨rfl, h2⟩ hne
  | trialityD4 =>
    obtain ⟨rfl, hce⟩ := GriessNative.chevalley_of_lieModel hmodel (by decide)
    exact GriessNative.trialityD4_row hce
  | twistedB2 =>
    obtain ⟨rfl, -⟩ := GriessNative.suzuki_of_lieModel hmodel
    exact GriessNative.twistedB2_row hmodel
  | twistedG2 =>
    obtain ⟨rfl, hR⟩ := GriessNative.reeTits_of_lieModel hmodel (by decide)
    exact GriessNative.twistedG2_row hR
  | twistedF4 =>
    obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hmodel (by decide)
    exact GriessNative.twistedF4_row hmodel
  | Tits =>
    obtain ⟨rfl, -⟩ := GriessNative.reeTits_of_lieModel hmodel (by decide)
    exact GriessNative.tits_row hmodel

end CFSG.ComponentClassification.Sol76T13.Hq4
