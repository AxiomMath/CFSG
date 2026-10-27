module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowData
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ComponentClassification.AS81.HeSylow

open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.Native

@[expose] def heSylLetters : Array (Array ℕ) := Array.ofFn fun j : Fin 9 => heInnerC1 j.val

@[expose] def heSylGen (i : ℕ) : Array ℕ :=
  wordA 8330 heSylLetters (heSylLetters.map (invCand 8330)) (heSylWords.getD i [])

@[expose] def heSylGens : Array (Array ℕ) := Array.ofFn fun i : Fin 5 => heSylGen i.val

@[expose] def heSylCert8330 : ArrCert := enumBfs 8330 heSylGens [0] 2000

@[expose] def sylCheck8330 : Bool :=
  heSylWords.length == 5 &&
    allLt 5 (fun i => lettersOK 9 (heSylWords.getD i [])) &&
    allLt 9 (fun j => validA 8330 heSylLetters[j]!) &&
    enumOK 8330 heSylGens [0] heSylCert8330 && heSylCert8330.pts.size == 1024

@[expose] def sylCheckRestrict : Bool :=
  heSylPts.size == 16 && heSyl16.length == 5 &&
    allLt 16 (fun k => decide (heSylPts[k]! < 8330)) &&
    allLt 15 (fun k => decide (heSylPts[k]! < heSylPts[k + 1]!)) &&
    allLt 5 fun i => validA 16 (heSyl16.getD i #[]) &&
      agreeOK 16 (heSylGen i) heSylPts (heSyl16.getD i #[])

@[expose] def ps16 : List ℕ := List.range 16

@[expose] def cert16 (gs : List (Array ℕ)) : ArrCert := enumBfs 16 gs.toArray ps16 4000

@[expose] def elts16 (gs : List (Array ℕ)) : List (Array ℕ) := (cert16 gs).pts.toList

@[expose] def enumCheck16 (gs : List (Array ℕ)) (m : ℕ) : Bool :=
  enumOK 16 gs.toArray ps16 (cert16 gs) && (cert16 gs).pts.size == m

@[expose] def inL (L : List (Array ℕ)) (t : Array ℕ) : Bool := L.any (eqA 16 t)

@[expose] def mul16 (a b : Array ℕ) : Array ℕ := compA 16 a b

@[expose] def comm16 (a b : Array ℕ) : Bool := eqA 16 (mul16 a b) (mul16 b a)

@[expose] def commZ (z a b : Array ℕ) : Bool :=
  comm16 a b || eqA 16 (mul16 a b) (mul16 (mul16 b a) z)

@[expose] def inZ (z t : Array ℕ) : Bool := eqA 16 t (idA 16) || eqA 16 t z

@[expose] def pow16 (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 16
  | k + 1 => mul16 a (pow16 a k)

@[expose] def setY (X : List (Array ℕ)) (z x : Array ℕ) : List (Array ℕ) :=
  X.filter fun y => inZ z (mul16 y y) && commZ z x y

@[expose] def uniqQOK (X Q : List (Array ℕ)) (z : Array ℕ) : Bool :=
  X.all fun x => inL Q x || !(inZ z (mul16 x x)) ||
    let Y := setY X z x
    decide (Y.length < 128) ||
      (Y.length == 128 && Y.any fun y => Y.any fun y' => !(commZ z y y'))

@[expose] def uniqEOK (X E F : List (Array ℕ)) : Bool :=
  X.all fun x => !(eqA 16 (mul16 x x) (idA 16)) || eqA 16 x (idA 16) || inL E x || inL F x ||
    decide ((X.filter fun y => eqA 16 (mul16 y y) (idA 16) && comm16 x y).length < 64)

@[expose] def sylCheck16 : Bool :=
  let X := elts16 heSyl16
  let Q := elts16 heSylQ16
  let E := elts16 heSylE16
  let F := elts16 heSylF16
  let U := elts16 heSylEz16
  let z := heSylZ16
  let r := heSylR16
  let s := heSylS16
  enumCheck16 heSyl16 1024 && enumCheck16 heSylQ16 128 && enumCheck16 heSylE16 64 &&
    enumCheck16 heSylF16 64 && enumCheck16 heSylEz16 16 &&
    validA 16 z && validA 16 r && validA 16 s &&
    heSylQ16.all (inL X) && heSylE16.all (inL X) && heSylF16.all (inL X) &&
    heSylEz16.all (inL Q) && inL Q z && inL X r && inL X s &&
    heSyl16.all (fun g => heSylQ16.all fun q => inL Q (conjA 16 g q)) &&
    heSyl16.all (fun g => heSylE16.all fun q => inL E (conjA 16 g q)) &&
    heSyl16.all (fun g => heSylF16.all fun q => inL F (conjA 16 g q)) &&
    eqA 16 (mul16 z z) (idA 16) && !(eqA 16 z (idA 16)) && heSyl16.all (comm16 z) &&
    X.all (fun x => !(heSyl16.all (comm16 x)) || inZ z x) &&
    Q.all (fun x => inZ z (mul16 x x)) &&
    Q.all (fun x => !(heSylQ16.all (comm16 x)) || inZ z x) &&
    heSylQ16.any (fun a => heSylQ16.any fun b => !(comm16 a b)) &&
    E.all (fun x => eqA 16 (mul16 x x) (idA 16)) &&
    heSylE16.all (fun a => heSylE16.all (comm16 a)) &&
    F.all (fun x => eqA 16 (mul16 x x) (idA 16)) &&
    heSylF16.all (fun a => heSylF16.all (comm16 a)) &&
    U.all (fun x => eqA 16 (mul16 x x) (idA 16)) &&
    heSylEz16.all (fun a => heSylEz16.all (comm16 a)) &&
    heSylE16.any (fun a => !(inL F a)) &&
    inL Q (pow16 r 4) && inL Q (mul16 s s) && inL Q (mul16 (mul16 s r) (mul16 s r)) &&
    !(inL Q r) && !(inL Q (pow16 r 2)) && !(inL Q (pow16 r 3)) &&
    !(inL Q s) && !(inL Q (mul16 s r)) && !(inL Q (mul16 s (pow16 r 2))) &&
    !(inL Q (mul16 s (pow16 r 3))) &&
    uniqQOK X Q z && uniqEOK X E F

@[expose] def heSylowCheck : Bool := sylCheck8330 && sylCheckRestrict && sylCheck16

end CFSG.ComponentClassification.AS81.HeSylow
