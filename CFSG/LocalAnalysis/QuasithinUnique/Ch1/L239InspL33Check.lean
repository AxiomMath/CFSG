module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Data

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L33Insp

set_option maxRecDepth 100000

@[expose] def dg (x k : Nat) : Nat := x / 3 ^ k % 3

@[expose] def pack (l : List Nat) : Nat :=
  l.getD 0 0 + 3 * l.getD 1 0 + 9 * l.getD 2 0 + 27 * l.getD 3 0 + 81 * l.getD 4 0 +
    243 * l.getD 5 0 + 729 * l.getD 6 0 + 2187 * l.getD 7 0 + 6561 * l.getD 8 0

@[expose] def nmul (x y : Nat) : Nat :=
  (dg x 0 * dg y 0 + dg x 1 * dg y 3 + dg x 2 * dg y 6) % 3 +
  3 * ((dg x 0 * dg y 1 + dg x 1 * dg y 4 + dg x 2 * dg y 7) % 3) +
  9 * ((dg x 0 * dg y 2 + dg x 1 * dg y 5 + dg x 2 * dg y 8) % 3) +
  27 * ((dg x 3 * dg y 0 + dg x 4 * dg y 3 + dg x 5 * dg y 6) % 3) +
  81 * ((dg x 3 * dg y 1 + dg x 4 * dg y 4 + dg x 5 * dg y 7) % 3) +
  243 * ((dg x 3 * dg y 2 + dg x 4 * dg y 5 + dg x 5 * dg y 8) % 3) +
  729 * ((dg x 6 * dg y 0 + dg x 7 * dg y 3 + dg x 8 * dg y 6) % 3) +
  2187 * ((dg x 6 * dg y 1 + dg x 7 * dg y 4 + dg x 8 * dg y 7) % 3) +
  6561 * ((dg x 6 * dg y 2 + dg x 7 * dg y 5 + dg x 8 * dg y 8) % 3)

@[expose] def ndet (x : Nat) : Nat :=
  (dg x 0 * dg x 4 * dg x 8 + 2 * (dg x 0 * dg x 5 * dg x 7) + 2 * (dg x 1 * dg x 3 * dg x 8) +
    dg x 1 * dg x 5 * dg x 6 + dg x 2 * dg x 3 * dg x 7 + 2 * (dg x 2 * dg x 4 * dg x 6)) % 3

@[expose] def nid : Nat := 1 + 81 + 6561

@[expose] def nt0 : Nat := 1 + 81 * 2 + 6561 * 2

@[expose] def nsq (x : Nat) : Nat := nmul x x

@[expose] def npow16 (x : Nat) : Nat := nsq (nsq (nsq (nsq x)))

@[expose] def nL : List Nat := (List.range 19683).filter fun x => ndet x == 1

@[expose] def c48p : List Nat := c48.map pack

@[expose] def t16p : List Nat := t16.map pack

@[expose] def q8p : List Nat := q8.map pack

@[expose] def q4p : Nat := pack q4

@[expose] def invTableP : List (Nat × Nat) := invTable.map fun e => (pack e.1, pack e.2)

theorem c48_check : ∀ c ∈ c48p, c < 19683 ∧ ndet c = 1 ∧ nmul c nt0 = nmul nt0 c := by decide +kernel

theorem invTable_check : ∀ e ∈ invTableP, e.1 < 19683 ∧ e.2 < 19683 ∧ ndet e.1 = 1 ∧ ndet e.2 = 1 ∧
    e.1 ≠ nid ∧ nmul e.1 e.1 = nid ∧ nmul e.2 nt0 = nmul e.1 e.2 := by decide +kernel

theorem inv_check : ∀ u ∈ nL, u ≠ nid → nmul u u = nid → u = nt0 ∨ ∃ e ∈ invTableP, e.1 = u := by
  decide +kernel

theorem t16_check : (∀ x ∈ t16p, ndet x = 1 ∧ nmul x nt0 = nmul nt0 x) ∧ nid ∈ t16p ∧
    (∀ x ∈ t16p, ∀ y ∈ t16p, nmul x y ∈ t16p) ∧ (∀ x ∈ t16p, ∃ y ∈ t16p, nmul x y = nid) ∧
    t16p.Nodup ∧ t16p.length = 16 ∧ (∀ x ∈ t16p, x < 19683) := by decide +kernel

theorem q8_check : (∀ x ∈ q8p, x ∈ t16p) ∧ nid ∈ q8p ∧ nt0 ∈ q8p ∧
    (∀ x ∈ q8p, x ≠ nid → x ≠ nt0 → nmul x x = nt0) ∧ q4p ∈ q8p ∧ q4p ≠ nid ∧ q4p ≠ nt0 := by
  decide +kernel

theorem t16_not_q8 : ∀ x ∈ t16p, x ∉ q8p →
    ∃ c ∈ c48p, ∃ y ∈ c48p, nmul c x = nmul y c ∧ npow16 (nmul x y) ≠ nid := by decide +kernel

end CFSG.QuasithinUnique.Vol2Native.L239.L33Insp
