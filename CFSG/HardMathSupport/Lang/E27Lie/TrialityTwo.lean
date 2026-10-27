module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityArith
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Classes
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglMain

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
  CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem two_pow_mod_three_even {n : ℕ} (hn : Even n) : (2 ^ n) % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : (2 ^ n) % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem card_isoPGUThree {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X] (h : IsoPGUThree X (2 ^ n)) :
    Nat.card X = (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Sec4.PiField false 2 n K := ⟨Nat.prime_two, hn, by rw [hK]; rfl⟩
  rw [Nat.card_congr e.toEquiv, Sec16.ProofKSL3Two.card_projImage_glPi hK',
    Sec13.card_slPi_three hK']
  simp only [Bool.cond_false]

theorem twentySeven_dvd_fixedSubgroup_trialityD4_two {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ n) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  obtain ⟨y, hy, hcard⟩ := exists_card_fixedSubgroup_eq_class hn hK hσ hα3 hαin
  rw [hcard]
  have hone : ∀ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, z = 1 →
      27 ∣ Nat.card (fixedSubgroup (MulAut.conj z * fieldActor σ σ)) := fun z hz => by
    rw [hz, map_one, one_mul, card_fixedSubgroup_sigma0 hn hK hσ]
    exact twentySeven_dvd_ordG2 _
  rcases hy with rfl | rfl
  · exact hone _ rfl
  · by_cases h1 : d4TrialityY0Elt K σ = 1
    · exact hone _ h1
    have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
    have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK3
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rcases Nat.even_or_odd n with he | ho
    · have := Tri2Pgl.card_autFix_y0_even hn he σ hK hσ
      rw [autFix_eq_fixedSubgroup] at this
      rw [this, ← mul_assoc]
      exact twentySeven_dvd_ordPGL3_even (two_pow_mod_three_even he)
    · obtain ⟨F, hF, hFf, hFc, ⟨e⟩⟩ := kF82D4SecondCentY0_holds n ho K σ hK hσ
      have := card_isoPGUThree hn ⟨F, hF, hFf, hFc, ⟨e⟩⟩
      rw [autFix_eq_fixedSubgroup] at this
      rw [this]
      exact twentySeven_dvd_ordPGU3 (two_pow_mod_three_odd ho)

end CFSG.HardMathSupport.Lang.E27Lie
