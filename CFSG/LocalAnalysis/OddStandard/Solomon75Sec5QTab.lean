module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.Solomon75Sec5QInputs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.OddStandard.Solomon75.AhatData
  Certificates.Solomon75Sec5Q

section Aux

variable {n : ℕ}

theorem factorial_eq_cardC (hn : 8 ≤ n) (hn' : n ≤ 11) :
    (n - 2 * 4).factorial * (2 ^ 4 * Nat.factorial 4) = cardC n := by
  interval_cases n <;> decide

end Aux

variable {n : ℕ} [NeZero n]

end CFSG.OddStandard.Solomon75
