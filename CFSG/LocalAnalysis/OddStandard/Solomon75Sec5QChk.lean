module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QFC
public import Certificates.Data.Solomon75Sec5QInputs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.OddStandard.Solomon75.AhatData
  Certificates.Solomon75Sec5Q

open scoped commutatorElement

variable {n : ℕ} [NeZero n]

namespace Chk

theorem c0_pow_three : swapsPerm 11 [(8, 9), (9, 10)] ^ 3 = 1 := by
  decide

theorem c0_ne_one : swapsPerm 11 [(8, 9), (9, 10)] ≠ 1 := by
  decide

theorem Bn_eleven : Bn 11 = zpowers (swapsPerm 11 [(8, 9), (9, 10)]) := by
  simp [Bn]

theorem Bn_of_ne (hn : n ≠ 11) : Bn n = ⊥ := by
  simp [Bn, hn]

end Chk

end CFSG.OddStandard.Solomon75
