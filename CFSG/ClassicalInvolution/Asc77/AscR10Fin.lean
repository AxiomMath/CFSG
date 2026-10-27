module

public import CFSG.ClassicalInvolution.Asc77.AscR10Nd
public import CFSG.ClassicalInvolution.Asc77.AscT3YFinal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.T3CII.T3W

variable (p f : ℕ) [Fact p.Prime]



theorem res10aNoConj_of_ne_nine (h9 : p ^ f ≠ 9) : Res10aNoConj p f := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb g
  exact d.r_noConj c7 c9 h8 h9 hb g

theorem res10aNoConj_of_nine (h : p ^ f = 9 → Res10aNoConj p f) : Res10aNoConj p f := by
  by_cases h9 : p ^ f = 9
  · exact h h9
  · exact res10aNoConj_of_ne_nine p f h9

theorem res10aNoConj_three_of_nine (h : p = 3 → f = 2 → Res10aNoConj p f) :
    p = 3 → Res10aNoConj p f := by
  intro hp3
  by_cases hf : f = 2
  · exact h hp3 hf
  · refine res10aNoConj_of_ne_nine p f fun h9 => hf ?_
    rw [hp3] at h9
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by rw [h9]; norm_num : 3 ^ f = 3 ^ 2)

theorem eq_three_two_of_pow_eq_nine (h : p ^ f = 9) : p = 3 ∧ f = 2 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h
  have hdvd : p ∣ 3 ^ 2 := by
    have : p ∣ p ^ f := dvd_pow_self p hf
    rw [h] at this
    simpa using this
  have hp : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow Fact.out hdvd)
  subst hp
  exact ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by rw [h]; norm_num : 3 ^ f = 3 ^ 2)⟩

theorem res10aNoConj_of_three_two (h : p = 3 → f = 2 → Res10aNoConj p f) : Res10aNoConj p f :=
  res10aNoConj_of_nine p f fun h9 => h (eq_three_two_of_pow_eq_nine p f h9).1
    (eq_three_two_of_pow_eq_nine p f h9).2

theorem t3CaseII_of_ne_nine (h9 : p ^ f ≠ 9) : T3CaseII p f :=
  t3CaseII_of_noConj p f (res10aNoConj_of_ne_nine p f h9)

theorem t3CaseII_of_nine (h : p ^ f = 9 → Res10aNoConj p f) : T3CaseII p f :=
  t3CaseII_of_noConj p f (res10aNoConj_of_nine p f h)

theorem t3CaseII_of_three_two (h : p = 3 → f = 2 → Res10aNoConj p f) : T3CaseII p f :=
  t3CaseII_of_noConj p f (res10aNoConj_of_three_two p f h)

theorem t3CaseII_three_of_nine (h : p = 3 → f = 2 → Res10aNoConj p f) :
    p = 3 → T3CaseII p f :=
  fun hp3 => t3CaseII_of_noConj p f (res10aNoConj_three_of_nine p f h hp3)

end CFSG.ClassicalInvolution.Asc77.T3CII
