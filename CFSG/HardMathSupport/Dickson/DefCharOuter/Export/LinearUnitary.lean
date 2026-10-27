module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.LinearTwo
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Unitary

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Yardstones.Md42047359a2a (lieFamily LieFamily)

theorem carrierOn_linearUnitary : CarrierOn .linearUnitary := by
  intro d hd _
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r q => exact carrier_A r q hv
  | twistedA r q => exact carrier_twistedA r q hv
  | _ => exact absurd hd (by simp [lieFamily])

theorem outerCentOn_linearUnitary : OuterCentOn .linearUnitary := by
  intro S _ _ hS hnc idx hfam he p hp hp2 hpc β hβ hout
  obtain ⟨e⟩ := he
  obtain ⟨d, hv⟩ := idx
  cases d with
  | A r q =>
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_A r q)
    rcases Nat.lt_or_ge r 2 with h1 | h2
    · obtain rfl : r = 1 := by omega
      exact outerCentData_A_one q hv e hp hp2 hpq hβ hout
    · exact outerCentData_A_of_two_le h2 q hv e hp hp2 hpq hβ hout
  | twistedA r q =>
    exact outerCentData_twistedA r q hv e hp hp2
      (hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedA r q)) hβ hout
  | _ => exact absurd hfam (by simp [lieFamily])

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
