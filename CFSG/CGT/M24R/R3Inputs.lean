module

public import CFSG.CGT.M24R.R3Data
public import CFSG.CGT.M24R.RelData
public import Certificates.Data.CFSGNative.Th.Tables
public import CFSG.Certificates.CosetEnumeration
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.CGT.M24R.R3

open CFSG.Sporadic.Th.Native CFSG.CosetTable CFSG.Certificates.CosetEnumeration

@[expose] def genTab : ℕ → Table
  | 0 => #[3, 1, 0, 2, 4, 22, 8, 6, 7, 9, 23, 11, 14, 12, 13, 15, 10, 5, 21, 19, 18, 20, 17, 16]
  | 1 => #[4, 1, 0, 3, 2, 20, 18, 13, 22, 9, 16, 11, 8, 21, 5, 15, 23, 6, 17, 19, 14, 7, 12, 10]
  | 2 => #[9, 1, 0, 3, 4, 14, 7, 8, 6, 2, 13, 11, 16, 17, 20, 15, 18, 10, 12, 19, 5, 23, 21, 22]
  | 3 => #[11, 1, 0, 3, 4, 17, 14, 21, 10, 9, 20, 2, 18, 7, 23, 15, 12, 22, 16, 19, 8, 13, 5, 6]
  | 4 => #[15, 1, 0, 3, 4, 7, 17, 16, 20, 9, 8, 11, 13, 14, 12, 2, 5, 18, 6, 19, 10, 22, 23, 21]
  | 5 => #[19, 1, 0, 3, 4, 16, 23, 5, 12, 9, 17, 11, 22, 10, 6, 15, 7, 13, 20, 2, 21, 18, 8, 14]
  | 6 => #[0, 5, 2, 3, 4, 1, 13, 16, 21, 9, 18, 11, 23, 6, 20, 15, 7, 22, 10, 19, 14, 8, 17, 12]
  | 7 => #[0, 6, 2, 3, 4, 13, 1, 8, 7, 9, 22, 11, 20, 5, 23, 15, 21, 18, 17, 19, 12, 16, 10, 14]
  | 8 => #[0, 7, 2, 3, 4, 16, 8, 1, 6, 9, 12, 11, 10, 21, 17, 15, 5, 14, 23, 19, 22, 13, 20, 18]
  | 9 => #[0, 10, 2, 3, 4, 18, 22, 12, 20, 9, 1, 11, 7, 17, 21, 15, 23, 13, 5, 19, 8, 14, 6, 16]
  | _ => idT 24

@[expose] def genTabInv : ℕ → Table
  | 0 => #[2, 1, 3, 0, 4, 17, 7, 8, 6, 9, 16, 11, 13, 14, 12, 15, 23, 22, 20, 19, 21, 18, 5, 10]
  | 1 => #[2, 1, 4, 3, 0, 14, 17, 21, 12, 9, 23, 11, 22, 7, 20, 15, 10, 18, 6, 19, 5, 13, 8, 16]
  | 2 => #[2, 1, 9, 3, 4, 20, 8, 6, 7, 0, 17, 11, 18, 10, 5, 15, 12, 13, 16, 19, 14, 22, 23, 21]
  | 3 => #[2, 1, 11, 3, 4, 22, 23, 13, 20, 9, 8, 0, 16, 21, 6, 15, 18, 5, 12, 19, 10, 7, 17, 14]
  | 4 => #[2, 1, 15, 3, 4, 16, 18, 5, 10, 9, 20, 11, 14, 12, 13, 0, 7, 6, 17, 19, 8, 23, 21, 22]
  | 5 => #[2, 1, 19, 3, 4, 7, 14, 16, 22, 9, 13, 11, 8, 17, 23, 15, 5, 10, 21, 0, 18, 20, 12, 6]
  | 6 => #[0, 5, 2, 3, 4, 1, 13, 16, 21, 9, 18, 11, 23, 6, 20, 15, 7, 22, 10, 19, 14, 8, 17, 12]
  | 7 => #[0, 6, 2, 3, 4, 13, 1, 8, 7, 9, 22, 11, 20, 5, 23, 15, 21, 18, 17, 19, 12, 16, 10, 14]
  | 8 => #[0, 7, 2, 3, 4, 16, 8, 1, 6, 9, 12, 11, 10, 21, 17, 15, 5, 14, 23, 19, 22, 13, 20, 18]
  | 9 => #[0, 10, 2, 3, 4, 18, 22, 12, 20, 9, 1, 11, 7, 17, 21, 15, 23, 13, 5, 19, 8, 14, 6, 16]
  | _ => idT 24

@[expose] def letTab (z : ℤ) : Table :=
  if 0 < z then genTab (z.toNat - 1) else genTabInv ((-z).toNat - 1)

@[expose] def letZ (l : Fin 10 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def wTab (w : N0Word) : Table := wordT 24 letTab (w.map letZ)

@[expose] def tabEq (a b : Table) : Bool := allIn 0 24 fun i => ap a i == ap b i

@[expose] def nEq (w w' : N0Word) : Bool := tabEq (wTab w) (wTab w')

@[expose] def relCheck : Bool := relsN8Ten.all fun r => nEq r []

@[expose] def identCheck : Bool :=
  nEq (thExp uD) (dExp uD) && nEq (nW ++ dExp uD ++ inv10 nW) (dExp bD) &&
    nEq (thExp bD) aW && !nEq aW [] &&
    (List.finRange 4).all (fun j =>
      nEq (inv10 nW ++ thExp (yD j) ++ nW) (dExp (a1D j)) &&
        nEq (nW ++ thExp (a1D j) ++ inv10 nW) (dExp (b1D j)) &&
        nEq (inv10 wW ++ dExp (yD j) ++ wW) (thExp (b1D j))) &&
    (List.finRange 16).all fun i => (List.finRange 4).all fun j =>
      nEq (eW i ++ dExp (yD j)) (dExp (yD j) ++ eW i)

@[expose] def distinctCheck : Bool :=
  ((List.finRange 16).all fun i => (List.finRange 16).all fun i' =>
    i == i' || !nEq (eW i) (eW i')) &&
  (List.finRange 16).all fun v => (List.finRange 16).all fun v' =>
    v == v' || !nEq (tWordOf v) (tWordOf v')

@[expose] def yTabs : List Table := (List.finRange 4).map fun j => wTab (dExp (yD j))

@[expose] def tupPts (ts : List Table) : List ℕ := ts.flatMap fun t => (List.range 24).map (ap t)

@[expose] def tupKey (ts : List Table) : ℕ := (tupPts ts).foldl (fun a d => a * 24 + d) 0

@[expose] def conjKey (z : N0Word) : ℕ :=
  tupKey (yTabs.map fun t => compT 24 (compT 24 (wTab (inv10 z)) t) (wTab z))

@[expose] def collRel (i : Fin 16) : M24Word :=
  (letG, true) :: nWord ++ (letG, true) :: invW nWord ++ (letG, true) ::
    invW (liftW10 (eW i ++ wW))

end CFSG.CGT.M24R.R3
