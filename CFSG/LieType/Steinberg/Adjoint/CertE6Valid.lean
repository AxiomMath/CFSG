module

public import CFSG.LieType.Steinberg.Adjoint.CertE6ValidInputs
public import Certificates.Certificate122

public import CFSG.LieType.Steinberg.Adjoint.CertE6Weyl
public import CFSG.LieType.Steinberg.Adjoint.CertE6Pairs
public import CFSG.LieType.Steinberg.Adjoint.Pairs
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate118

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

theorem e6AdjData_nR : AdjData.nR .E6 = 72 := by
  exact Certificates.certificate122

theorem e6AdjData_checkWeyl : e6AdjData.checkWeyl = true := by
  rw [AdjData.checkWeyl, e6AdjData_nR, show (72 : ℕ) = 3 * 24 from rfl]
  refine e6AdjData.checkWeylRange_of_slices 0 24 3 fun s hs => ?_
  interval_cases s
  exacts [e6AdjData_checkWeyl_0, e6AdjData_checkWeyl_1, e6AdjData_checkWeyl_2]

theorem e6AdjData_checkPairs : e6AdjData.checkPairs = true := by
  rw [AdjData.checkPairs, e6AdjData_nR, show (72 : ℕ) = 3 * 24 from rfl]
  refine e6AdjData.checkPairsRange_of_slices 0 24 3 fun s hs => ?_
  interval_cases s
  exacts [e6AdjData_checkPairs_0, e6AdjData_checkPairs_1, e6AdjData_checkPairs_2]

theorem e6AdjData_valid : e6AdjData.Valid :=
  ⟨e6AdjData_checkTables, e6AdjData_checkSimple, e6AdjData_checkWeyl, e6AdjData_checkPairs,
    e6AdjData_checkPairNorm⟩

end CFSG.LieType.Steinberg.Adjoint
