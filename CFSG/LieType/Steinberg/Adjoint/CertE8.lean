module

public import CFSG.LieType.Steinberg.Adjoint.CertE8Inputs
public import Certificates.Certificate120

public import CFSG.LieType.Steinberg.Adjoint.CertE8Weyl
public import CFSG.LieType.Steinberg.Adjoint.CertE8Pairs
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e8Data_nR : AdjData.nR .E8 = 240 := by
  exact Certificates.certificate120

theorem e8Data_checkWeyl : e8Data.checkWeyl = true := by
  rw [AdjData.checkWeyl, e8Data_nR, show (240 : ℕ) = 12 * 20 from rfl]
  refine e8Data.checkWeylRange_of_slices 0 20 12 fun s hs => ?_
  interval_cases s
  exacts [e8Data_checkWeyl_0, e8Data_checkWeyl_1, e8Data_checkWeyl_2, e8Data_checkWeyl_3,
    e8Data_checkWeyl_4, e8Data_checkWeyl_5, e8Data_checkWeyl_6, e8Data_checkWeyl_7,
    e8Data_checkWeyl_8, e8Data_checkWeyl_9, e8Data_checkWeyl_10, e8Data_checkWeyl_11]

theorem e8Data_checkPairs : e8Data.checkPairs = true := by
  rw [AdjData.checkPairs, e8Data_nR, show (240 : ℕ) = 12 * 20 from rfl]
  refine e8Data.checkPairsRange_of_slices 0 20 12 fun s hs => ?_
  interval_cases s
  exacts [e8Data_checkPairs_0, e8Data_checkPairs_1, e8Data_checkPairs_2, e8Data_checkPairs_3,
    e8Data_checkPairs_4, e8Data_checkPairs_5, e8Data_checkPairs_6, e8Data_checkPairs_7,
    e8Data_checkPairs_8, e8Data_checkPairs_9, e8Data_checkPairs_10, e8Data_checkPairs_11]

theorem e8Data_check : e8Data.checkTables = true ∧ e8Data.checkSimple = true ∧
    e8Data.checkWeyl = true ∧ e8Data.checkPairs = true :=
  ⟨e8Data_checkTables, e8Data_checkSimple, e8Data_checkWeyl, e8Data_checkPairs⟩

end CFSG.LieType.Steinberg.Adjoint
