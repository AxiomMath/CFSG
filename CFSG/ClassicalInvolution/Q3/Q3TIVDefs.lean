module

public import CFSG.ClassicalInvolution.Q3.Q3TPCtx

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TP


@[expose] def TwinProductCentral3 (tY : StatedLieTag) (nY : ℕ) : Prop :=
  ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∀ R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      R ≠ R' → Commutes R R' →
      (∀ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
        (S = R ∨ Commutes S R) ↔ (S = R' ∨ Commutes S R')) →
      ∀ r ∈ R, (∀ s ∈ R, r * s = s * r) → r ≠ 1 →
      ∀ r' ∈ R', (∀ s ∈ R', r' * s = s * r') → r' ≠ 1 →
        r * r' ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K

structure TwinRowFacts3 (tY : StatedLieTag) (nY : ℕ) : Prop where
  y : YData3S tY nY
  nonempty : ∃ R, R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D
  nc : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∃ S ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      S ≠ R ∧ ¬ Commutes S R

end CFSG.ClassicalInvolution.Q3.Q3TIV
