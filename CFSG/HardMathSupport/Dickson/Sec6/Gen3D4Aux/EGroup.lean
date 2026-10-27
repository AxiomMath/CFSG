module

public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.Real
public import CFSG.HardMathSupport.Dickson.Sec6.Gen3D4Aux.EData

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.Gen3D4

@[expose] def eWord (c i : ℕ) : List ℕ := (eWords.getD c []).getD i []

@[expose] def ePTable : Array Pr :=
  #[wordP (eWord 0 0), wordP (eWord 0 1), wordP (eWord 0 2), wordP (eWord 1 0), wordP (eWord 1 1),
    wordP (eWord 1 2), wordP (eWord 2 0), wordP (eWord 2 1), wordP (eWord 2 2), wordP (eWord 3 0),
    wordP (eWord 3 1), wordP (eWord 3 2)]

@[expose] def eP (c i : ℕ) : Pr := ePTable.getD (3 * c + i) oneP

theorem eP_eq {c i : ℕ} (hc : c < 4) (hi : i < 3) : eP c i = wordP (eWord c i) := by
  interval_cases c <;> interval_cases i <;> rfl

namespace Realization

variable {X : Type} [Group X] (R : Realization X)

@[expose] def ea (c i : ℕ) : X := R.wordElt (eWord c i)

@[expose] def Eg (c : ℕ) : Subgroup X := Subgroup.closure {R.ea c 0, R.ea c 1, R.ea c 2}

end Realization

end CFSG.HardMathSupport.Dickson.Sec6.Gen3D4
