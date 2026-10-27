module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Q47Data
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeAutSylowTests

public section

namespace CFSG.ComponentClassification.AS81.N48

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow CFSG.ComponentClassification.AS81.Q47

@[expose] def nInv : List (Array ℕ) :=
  (eltsN 64 q47NGens).filter fun a => eqA 64 (mulN 64 a a) (idA 64)

@[expose] def fixTab (a b : Array ℕ) : Array Bool :=
  Array.ofFn fun c : Fin 64 => a[c.val]! == c.val && b[c.val]! == c.val

@[expose] def cnt (t : Array Bool) : ℕ :=
  (Finset.univ.filter fun w : Fin 64 => t[w.val]! = true).card

@[expose] def spanTab (a b : Array ℕ) (C : Array Bool) : Array Bool :=
  Array.ofFn fun w : Fin 64 => C[w.val]! || (List.range 64).any fun v =>
    C[w.val ^^^ v ^^^ a[v]!]! || C[w.val ^^^ v ^^^ b[v]!]! || C[w.val ^^^ v ^^^ a[b[v]!]!]!

@[expose] def fourCheck (a b : Array ℕ) (C S : Array Bool) : Bool :=
  (decide (16 ≤ cnt (fixTab a a)) || decide (16 ≤ cnt (fixTab b b)) ||
      decide (16 ≤ cnt (fixTab (mulN 64 a b) (mulN 64 a b)))) &&
    (decide (cnt S < 16) || (decide (cnt C ≤ 4) &&
      (List.range 64).any fun x => !S[x]! &&
        (C[x ^^^ a[x]!]! || C[x ^^^ b[x]!]! || C[x ^^^ a[b[x]!]!]!)))

@[expose] def pairCheck (a b : Array ℕ) : Bool :=
  let C := fixTab a b
  let S := spanTab a b C
  !(commN 64 a b) || (eqA 64 a (idA 64) && eqA 64 b (idA 64)) ||
    (decide (cnt S ≤ 16) &&
      (eqA 64 a (idA 64) || eqA 64 b (idA 64) || eqA 64 a b || fourCheck a b C S))

@[expose] def rankCheck : Bool :=
  nInv.all fun a => nInv.all fun b => nInv.all fun c =>
    !(commN 64 a b) || !(commN 64 a c) || !(commN 64 b c) || eqA 64 a (idA 64) ||
      eqA 64 b (idA 64) || eqA 64 b a || eqA 64 c (idA 64) || eqA 64 c a || eqA 64 c b ||
        eqA 64 c (mulN 64 a b)

@[expose] def n48Check : Bool :=
  enumCheckN 64 q47NGens 336 && rankCheck && nInv.all fun a => nInv.all fun b => pairCheck a b

end CFSG.ComponentClassification.AS81.N48
