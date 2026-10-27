module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueCP
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFC

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem E0_unique :
    ∀ B : Subgroup ↥Cd, B ≤ normalizer (E0 : Set ↥Cd) → (∀ b ∈ B, b ^ 2 = 1) →
      Nat.card B = 2 ^ 11 → B = E0 :=
  E0_unique_of_cp fun _ hA hsq hcard hE => cp_of_fc fcSpec_data hA hsq hcard hE

end CFSG.EvenSporadicStandard.TwoFi22.DS81
