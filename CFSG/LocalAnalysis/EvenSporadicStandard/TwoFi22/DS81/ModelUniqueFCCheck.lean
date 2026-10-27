module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueLin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueData
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCData

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

set_option compiler.extract_closed false

@[expose] def fcMatEq (a b : Array Nat) : Bool :=
  a[0]! == b[0]! && a[1]! == b[1]! && a[2]! == b[2]! && a[3]! == b[3]! && a[4]! == b[4]! &&
    a[5]! == b[5]! && a[6]! == b[6]! && a[7]! == b[7]! && a[8]! == b[8]! && a[9]! == b[9]!

@[expose] def fcColsLt (a : Array Nat) : Bool :=
  a[0]! < 1024 && a[1]! < 1024 && a[2]! < 1024 && a[3]! < 1024 && a[4]! < 1024 &&
    a[5]! < 1024 && a[6]! < 1024 && a[7]! < 1024 && a[8]! < 1024 && a[9]! < 1024

@[expose] def fcMatEqAct (m t r : Array Nat) : Bool :=
  m[0]! == t[r[0]!]! && m[1]! == t[r[1]!]! && m[2]! == t[r[2]!]! && m[3]! == t[r[3]!]! &&
    m[4]! == t[r[4]!]! && m[5]! == t[r[5]!]! && m[6]! == t[r[6]!]! && m[7]! == t[r[7]!]! &&
    m[8]! == t[r[8]!]! && m[9]! == t[r[9]!]!

@[expose] def fcIdx (ms : Array (Array Nat)) (r : Array Nat) : Nat := ms.findIdx (fcMatEq r)

@[expose] def fcAct (c : Array Nat) : Array Nat := (Array.range 1024).map (lin c)

@[expose] def fcMul (ms act : Array (Array Nat)) : Array (Array Nat) :=
  act.map fun t => ms.map fun r => ms.findIdx fun m => fcMatEqAct m t r

@[expose] def fcDistinct (ms : Array (Array Nat)) : Bool :=
  (List.range ms.size).all fun i => (List.range ms.size).all fun j =>
    !fcMatEq ms[i]! ms[j]! || i == j

@[expose] def fcHits (ia : Array Nat) (n : Nat) : List Nat :=
  (List.range n).filter fun x => ia.contains x

@[expose] def fcCover (tab : Array (Array Nat)) (A B : List Nat) (n : Nat) : Bool :=
  (List.range n).all fun i => A.any fun x => B.any fun y => tab[x]![y]! == i

@[expose] def fcExt (tab : Array (Array Nat)) (Y : List Nat) (y : Nat) : List Nat :=
  (Y ++ Y.map fun x => tab[y]![x]!).mergeSort (fun a b => decide (a ≤ b))

@[expose] def fcExtOK (tab : Array (Array Nat)) (e n : Nat) (fam : List (List Nat)) : Bool :=
  fam.all fun Y => (List.range n).all fun y =>
    !(tab[y]![y]! == e && !Y.contains y && Y.all fun x => tab[y]![x]! == tab[x]![y]!) ||
      fam.contains (fcExt tab Y y)

@[expose] def fcFix (act : Array (Array Nat)) (Z : List Nat) : Nat :=
  ((List.range 1024).filter fun v => Z.all fun x => act[x]![v]! == v).length

@[expose] def fcFixOK (act : Array (Array Nat)) (e : Nat) (fam : List (List Nat)) : Bool :=
  fam.all fun Z => Z == [e] || decide (Z.length * fcFix act Z ≤ 2 ^ 9)

@[expose] def fcCore (cu cw ms : Array (Array Nat)) (fam : List (List Nat))
    (act tab : Array (Array Nat)) (e : Nat) (ia ib : Array Nat) : Bool :=
  cu.all fcColsLt && cw.all fcColsLt && ms.all fcColsLt && decide (2 ^ 7 ≤ ms.size) &&
    fcDistinct ms && tab.all (·.all (· < ms.size)) && ia.all (· < ms.size) &&
    ib.all (· < ms.size) && fcCover tab (fcHits ia ms.size) (fcHits ib ms.size) ms.size &&
    decide (e < ms.size) && fam.contains [e] && fcExtOK tab e ms.size fam && fcFixOK act e fam

@[expose] def fcCheck (cu cw ms : Array (Array Nat)) (fam : List (List Nat)) : Bool :=
  let act := ms.map fcAct
  fcCore cu cw ms fam act (fcMul ms act) (fcIdx ms idCols) (cu.map (fcIdx ms))
    (cw.map (fcIdx ms))

@[expose] def fcCertificate : Bool :=
  fcCheck (uqCols uqW uqSg0) (uqCols uqW uqSg1) uqMs uqFam

end CFSG.EvenSporadicStandard.TwoFi22.DS81
