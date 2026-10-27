module

public import Certificates.Data.Asc82Fact59
import all Certificates.Data.Asc82Fact59
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega.Fact59Bridge

open CFSG.OddStandard.SmallF3.Omega.Fact59Check

@[expose] def vecOfNat (n : ℕ) : Fin 6 → ZMod 2 :=
  fun i => if n.testBit i.val then 1 else 0

@[expose] def natOfVec (v : Fin 6 → ZMod 2) : ℕ :=
  ∑ i : Fin 6, (v i).val * 2 ^ i.val

theorem natOfVec_lt (v : Fin 6 → ZMod 2) : natOfVec v < 64 := by
  revert v
  decide +kernel

theorem vecOfNat_natOfVec (v : Fin 6 → ZMod 2) : vecOfNat (natOfVec v) = v := by
  revert v
  decide +kernel

end CFSG.OddStandard.SmallF3.Omega.Fact59Bridge
