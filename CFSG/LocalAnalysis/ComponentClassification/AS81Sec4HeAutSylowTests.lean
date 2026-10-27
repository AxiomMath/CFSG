
module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] def certN (n : ℕ) (gs : List (Array ℕ)) : ArrCert :=
  enumBfs n gs.toArray (List.range n) 4000

@[expose] def eltsN (n : ℕ) (gs : List (Array ℕ)) : List (Array ℕ) := (certN n gs).pts.toList

@[expose] def enumCheckN (n : ℕ) (gs : List (Array ℕ)) (m : ℕ) : Bool :=
  enumOK n gs.toArray (List.range n) (certN n gs) && (certN n gs).pts.size == m

@[expose] def inLN (n : ℕ) (L : List (Array ℕ)) (t : Array ℕ) : Bool := L.any (eqA n t)

@[expose] def mulN (n : ℕ) (a b : Array ℕ) : Array ℕ := compA n a b

@[expose] def commN (n : ℕ) (a b : Array ℕ) : Bool := eqA n (mulN n a b) (mulN n b a)

@[expose] def commZN (n : ℕ) (z a b : Array ℕ) : Bool :=
  commN n a b || eqA n (mulN n a b) (mulN n (mulN n b a) z)

@[expose] def inZN (n : ℕ) (z t : Array ℕ) : Bool := eqA n t (idA n) || eqA n t z

@[expose] def powN (n : ℕ) (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => mulN n a (powN n a k)

@[expose] def setYN (n : ℕ) (X : List (Array ℕ)) (z x : Array ℕ) : List (Array ℕ) :=
  X.filter fun y => inZN n z (mulN n y y) && commZN n z x y

@[expose] def goodQN (n : ℕ) (X : List (Array ℕ)) (z x : Array ℕ) : Bool :=
  let Y := setYN n X z x
  decide (Y.length < 128) || (Y.length == 128 && Y.any fun y => Y.any fun y' => !(commZN n z y y'))

@[expose] def uniqQN (n : ℕ) (X Q : List (Array ℕ)) (z : Array ℕ) : Bool :=
  decide ((X.filter fun x => !(inLN n Q x) && inZN n z (mulN n x x) && !(goodQN n X z x)).length <
    64)

@[expose] def uniqEN (n : ℕ) (X E F : List (Array ℕ)) : Bool :=
  X.all fun x => !(eqA n (mulN n x x) (idA n)) || eqA n x (idA n) || inLN n E x || inLN n F x ||
    decide ((X.filter fun y => eqA n (mulN n y y) (idA n) && commN n x y).length < 64)

@[expose] def heAutSylowCheck : Bool :=
  let gs := hfT0Tabs32.toList
  let X := eltsN 32 gs
  let Q := eltsN 32 heAutQ32
  let E := eltsN 32 heAutE32
  let F := eltsN 32 heAutF32
  let U := eltsN 32 heAutU32
  let z := heAutZ32
  let r := heAutR32
  let s := heAutS32
  enumCheckN 32 gs 2048 && enumCheckN 32 heAutQ32 128 && enumCheckN 32 heAutE32 64 &&
    enumCheckN 32 heAutF32 64 && enumCheckN 32 heAutU32 16 &&
    validA 32 z && validA 32 r && validA 32 s &&
    heAutQ32.all (inLN 32 X) && heAutE32.all (inLN 32 X) && heAutF32.all (inLN 32 X) &&
    heAutU32.all (inLN 32 Q) && inLN 32 Q z && inLN 32 X r && inLN 32 X s &&
    gs.all (fun g => heAutQ32.all fun q => inLN 32 Q (conjA 32 g q)) &&
    heAutQ32.all (fun g => heAutE32.all fun q => inLN 32 E (conjA 32 g q)) &&
    heAutQ32.all (fun g => heAutF32.all fun q => inLN 32 F (conjA 32 g q)) &&
    eqA 32 (mulN 32 z z) (idA 32) && !(eqA 32 z (idA 32)) && gs.all (commN 32 z) &&
    X.all (fun x => !(gs.all (commN 32 x)) || inZN 32 z x) &&
    Q.all (fun x => inZN 32 z (mulN 32 x x)) &&
    Q.all (fun x => !(heAutQ32.all (commN 32 x)) || inZN 32 z x) &&
    heAutQ32.any (fun a => heAutQ32.any fun b => !(commN 32 a b)) &&
    E.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    heAutE32.all (fun a => heAutE32.all (commN 32 a)) &&
    F.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    heAutF32.all (fun a => heAutF32.all (commN 32 a)) &&
    U.all (fun x => eqA 32 (mulN 32 x x) (idA 32)) &&
    heAutU32.all (fun a => heAutU32.all (commN 32 a)) &&
    heAutE32.any (fun a => !(inLN 32 F a)) &&
    inLN 32 Q (powN 32 r 8) && inLN 32 Q (mulN 32 s s) &&
    inLN 32 Q (mulN 32 (mulN 32 s r) (mulN 32 s r)) &&
    (List.range 7).all (fun i => !(inLN 32 Q (powN 32 r (i + 1)))) &&
    (List.range 8).all (fun i => !(inLN 32 Q (mulN 32 s (powN 32 r i)))) &&
    uniqQN 32 X Q z && uniqEN 32 X E F

end CFSG.ComponentClassification.AS81.HeSylow
