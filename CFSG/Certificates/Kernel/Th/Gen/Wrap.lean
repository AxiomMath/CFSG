module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS

public section

namespace CFSG.KC.Th.Gen

@[expose] noncomputable def eqN (a b : Nat) : Bool := Nat.beq a b
@[expose] noncomputable def neN (a b : Nat) : Bool := BigS.notB (Nat.beq a b)
@[expose] noncomputable def ltN (a b : Nat) : Bool := Nat.blt a b
@[expose] noncomputable def leN (a b : Nat) : Bool := Nat.ble a b

theorem eqN_of {a b : Nat} (h : Nat.beq a b = true) : eqN a b = true := h
theorem neN_of {a b : Nat} (h : BigS.notB (Nat.beq a b) = true) : neN a b = true := h
theorem neN_of' {a b : Nat} (h : DceS.notB (Nat.beq a b) = true) : neN a b = true := h
theorem ltN_of {a b : Nat} (h : Nat.blt a b = true) : ltN a b = true := h
theorem leN_of {a b : Nat} (h : Nat.ble a b = true) : leN a b = true := h

theorem andB_left {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : a = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · rfl

theorem andB_right {a b : Bool} (h : CFSG.KC.Th.andB a b = true) : b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact h

end CFSG.KC.Th.Gen
