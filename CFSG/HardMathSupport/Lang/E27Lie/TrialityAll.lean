module

public import CFSG.HardMathSupport.Lang.E27Lie.MinusToral
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThree
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityOddFinal

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)



theorem twentySeven_dvd_fixedSubgroup_trialityD4_model {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Group K] [Finite K]
    (hmodel : CFSG.Blueprint.TwistedChevalleyModel K .D4 (p ^ f))
    (α : MulAut K) (hα3 : α ^ 3 = 1) (hαin : α ∉ inner K) :
    27 ∣ Nat.card (fixedSubgroup α) := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · exact twentySeven_dvd_fixedSubgroup_trialityD4_two_model hf K hmodel α hα3 hαin
  · by_cases h3 : p = 3
    · subst h3
      exact twentySeven_dvd_fixedSubgroup_trialityD4_three_model hf K hmodel α hα3 hαin
    · have hp5 : 5 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨k, hk⟩
        omega
      have hq3 : ¬ 3 ∣ p ^ f := fun h =>
        h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
          (Nat.prime_three.dvd_of_dvd_pow h)).symm
      have hq : (p ^ f) % 3 = 1 ∨ (p ^ f) % 3 = 2 := by omega
      rcases hq with hq | hq
      · exact twentySeven_dvd_fixedSubgroup_trialityD4_q1_model hp hp5 hf hq K hmodel α hα3 hαin
      · exact twentySeven_dvd_fixedSubgroup_trialityD4_q2_model minusToralLower_holds hp hp5 hf K
          hmodel α hα3 hαin

end CFSG.HardMathSupport.Lang.E27Lie
