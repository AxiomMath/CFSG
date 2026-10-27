module

public import CFSG.ClassicalInvolution.Q3.Q3T7Q22Rows

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic


@[expose] def TwinPairShape3 : Prop :=
  ∀ (t : StatedLieTag) (n : ℕ), IsFundTag t → StatedLieAdmissible t n 3 1 →
    ∀ (H : Type) [Group H] [Finite H]
      (ψ : (modelUniv t n 3 1 Nat.prime_three).K →* H)
      (R R' : Subgroup (modelUniv t n 3 1 Nat.prime_three).K)
      (x x' : (modelUniv t n 3 1 Nat.prime_three).K),
      TwinPairOn t (modelUniv t n 3 1 Nat.prime_three) ψ R R' x x' →
        TwinShape t n ∨ t = .G2 ∨ t = .trialityD4

theorem twinSqAlphaAll3_of_rows (hshape : TwinPairShape3) (hrows : TwinSqRows3)
    (hG2 : ∀ n, StatedLieAdmissible .G2 n 3 1 → TwinSqAlpha 3 1 .G2 n)
    (hD4 : ∀ n, StatedLieAdmissible .trialityD4 n 3 1 → TwinSqAlpha 3 1 .trialityD4 n) :
    TwinSqAlphaAll3 := by
  intro t n ht hadm H _ _ ψ R R' x x' hpair
  rcases hshape t n ht hadm H ψ R R' x x' hpair with hsh | rfl | rfl
  · exact twinSqAlphaRows3_of_rows hrows t n hadm hsh H ψ R R' x x' hpair
  · exact hG2 n hadm H ψ R R' x x' hpair
  · exact hD4 n hadm H ψ R R' x x' hpair

theorem twinOuterAlphaAll3_of_rows (hshape : TwinPairShape3) (hrows : TwinOuterRows3)
    (hG2 : ∀ n, StatedLieAdmissible .G2 n 3 1 → TwinOuterAlpha 3 1 .G2 n)
    (hD4 : ∀ n, StatedLieAdmissible .trialityD4 n 3 1 → TwinOuterAlpha 3 1 .trialityD4 n) :
    TwinOuterAlphaAll3 := by
  intro t n ht hadm H _ _ ψ R R' x x' hpair
  rcases hshape t n ht hadm H ψ R R' x x' hpair with hsh | rfl | rfl
  · exact twinOuterAlphaRows3_of_rows hrows t n hadm hsh H ψ R R' x x' hpair
  · exact hG2 n hadm H ψ R R' x x' hpair
  · exact hD4 n hadm H ψ R R' x x' hpair

end CFSG.ClassicalInvolution.Q3.Q3T7
