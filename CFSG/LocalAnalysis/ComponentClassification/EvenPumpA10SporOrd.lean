module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Comps

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint

theorem a10SporClause_M11 :
    A10SporClauseFor .M11 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M11) = Nat.card NativeSporadic.M11 from rfl,
      Sporadic.Mathieu.card_M11]
    decide)

theorem a10SporClause_M12 :
    A10SporClauseFor .M12 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M12) = Nat.card NativeSporadic.M12 from rfl,
      Sporadic.Mathieu.card_M12]
    decide)

theorem a10SporClause_M22 :
    A10SporClauseFor .M22 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M22) = Nat.card NativeSporadic.M22 from rfl,
      Sporadic.Mathieu.card_M22]
    decide)

theorem a10SporClause_M23 :
    A10SporClauseFor .M23 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M23) = Nat.card NativeSporadic.M23 from rfl,
      Sporadic.Schreier.m23_card]
    decide)

theorem a10SporClause_M24 :
    A10SporClauseFor .M24 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .M24) = Nat.card NativeSporadic.M24 from rfl,
      Sporadic.Mathieu.card_M24]
    decide)

theorem a10SporClause_J1 :
    A10SporClauseFor .J1 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J1) = Nat.card NativeSporadic.J1 from rfl,
      Sporadic.J1.card_J1]
    decide)

theorem a10SporClause_J2 :
    A10SporClauseFor .J2 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J2) = Nat.card NativeSporadic.J2 from rfl,
      Sporadic.J2.card_J2]
    decide)

theorem a10SporClause_J3 :
    A10SporClauseFor .J3 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
      Sporadic.J3.card_J3]
    decide)

theorem a10SporClause_J4 :
    A10SporClauseFor .J4 :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .J4) = Nat.card NativeSporadic.J4 from rfl,
      Sporadic.J4.card_J4]
    decide)

theorem a10SporClause_HS :
    A10SporClauseFor .HS :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .HS) = Nat.card NativeSporadic.HS from rfl,
      Sporadic.HS.card_HS]
    decide)

theorem a10SporClause_He :
    A10SporClauseFor .He :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .He) = Nat.card NativeSporadic.He from rfl,
      Sporadic.He.card_He]
    decide)

theorem a10SporClause_Ru :
    A10SporClauseFor .Ru :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .Ru) = Nat.card NativeSporadic.Ru from rfl,
      Sporadic.Ru.card_Ru]
    decide)

theorem a10SporClause_ONan :
    A10SporClauseFor .ONan :=
  a10SporClauseFor_of_card (by
    rw [show Nat.card (NativeSporadic.Carrier .ONan) = Nat.card NativeSporadic.ON from rfl,
      Sporadic.ONOddCore.card_native_ON]
    decide)

end CFSG.ComponentClassification.EvenPump
