module

public import CFSG.Sporadic.SmallOddCore.CentData

public section

namespace CFSG.EvenSmallLie.Child3.SelK3

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native

inductive Wit where
  | z4 (w : Nat)
  | v4 (u v : Nat)

@[expose] def instrLtB (r : Nat) : Instr → Bool
  | .mu i j k => i < r && j < r && k < r
  | .pwr _ i k => i < r && k < r
  | .iv i k => i < r && k < r

@[expose] def parseInstr (l : String) : Option Instr :=
  let num (t : String) : Nat := t.toNat?.getD 0
  match l.splitOn " " with
  | ["m", i, j, k] => some (.mu (num i) (num j) (num k))
  | ["p", e, i, k] => some (.pwr (num e) (num i) (num k))
  | ["v", i, k] => some (.iv (num i) (num k))
  | _ => none

@[expose] def parseProg (s : String) : List Instr := (s.splitOn "\n").filterMap parseInstr

structure Data where
  n : Nat
  gens : Array Table
  regs : Nat
  prog : List Instr
  syl : List Nat
  order : Nat
  reps : List Nat
  wits : List Wit

@[expose] def regs0 (D : Data) : Array Table :=
  D.gens ++ Array.replicate (D.regs - D.gens.size) (idT D.n)

@[expose] def isOrd3 (n : Nat) (T : Table) : Bool := !tblEq n T (idT n) && order3OK n T

@[expose] def witOK (n : Nat) (regs : Array Table) (x : Table) : Wit → Bool
  | .z4 w => w < regs.size && commTT n regs[w]! x &&
      !tblEq n (compT n regs[w]! regs[w]!) (idT n) && tblEq n (powT n 4 regs[w]!) (idT n)
  | .v4 u v => u < regs.size && v < regs.size && involOK n regs[u]! && involOK n regs[v]! &&
      !tblEq n regs[u]! regs[v]! && commTT n regs[u]! regs[v]! && commTT n regs[u]! x &&
      commTT n regs[v]! x

@[expose] def checkCore (n order : Nat) (regs : Array Table) (syl reps : List Nat)
    (wits : List Wit) : Bool :=
  let A := (syl.map fun r => regs[r]!).toArray
  let Ai := A.map (invT n)
  let E := mulClosureH n A (order + 1)
  let R := reps.map fun i => E.1[i]!
  let C := R.map fun x => conjClosureH n A Ai x (order + 1)
  syl.all (· < regs.size) && A.all (permOK n) && A.all (fun x => invOK n x (invT n x)) &&
    mulTreeOK n A E.1 E.2.1 E.2.2 && closedOK n (A ++ Ai) E.1 &&
    hkeysDistinct n E.1.toList && E.1.size == order && reps.all (· < E.1.size) &&
    reps.length == wits.length &&
    (R.zip C).all (fun p => conjTreeOK n A Ai p.1 p.2.1 p.2.2.1 p.2.2.2) &&
    E.1.all (fun e => !isOrd3 n e || C.any fun c => memT n c.1 e || memT n c.1 (compT n e e)) &&
    (R.zip wits).all (fun p => witOK n regs p.1 p.2)

@[expose] def check (D : Data) : Bool :=
  let s := runSLP D.n D.prog (regs0 D)
  D.gens.size ≤ D.regs && D.prog.all (instrLtB D.regs) && s.2 &&
    checkCore D.n D.order s.1 D.syl D.reps D.wits

end CFSG.EvenSmallLie.Child3.SelK3
