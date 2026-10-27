
module

public import Certificates.Data.CFSGNative.Fischer.Polar
public import CFSG.Certificates.Kernel.U6Sound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.NativeDataBase

public section

namespace CFSG.KC.U6

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
  CFSG.EvenSmallLie.UnitarySix CFSG.Fischer.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def tvTabsG (pts pos : Array ℕ) : Array Table :=
  Array.ofFn (n := 693) fun p => tvTableG pts pos pts[p.val]!

variable (L : List (Equiv.Perm (Fin 693)))

@[expose] def u62WG (w : List ℤ) : Equiv.Perm (Fin 693) := tab (evalCodes L w)

@[expose] def aGensG (aw : List (List ℤ)) : List (Equiv.Perm (Fin 693)) := aw.map (u62WG L)

@[expose] def kGensG (kw : List (List ℤ)) : List (Equiv.Perm (Fin 693)) := kw.map (u62WG L)

@[expose] def j1G (aw : List (List ℤ)) : Equiv.Perm (Fin 693) := evalCodes (aGensG L aw) [1]
@[expose] def j2G (aw : List (List ℤ)) : Equiv.Perm (Fin 693) := evalCodes (aGensG L aw) [2, 5]
@[expose] def j3G (aw : List (List ℤ)) : Equiv.Perm (Fin 693) := evalCodes (aGensG L aw) [1, 2, 5]
@[expose] def c3G (aw : List (List ℤ)) : Equiv.Perm (Fin 693) := evalCodes (aGensG L aw) [3]

@[expose] def sumCheckG (aw : List (List ℤ)) : Bool :=
  (fixedList 693 (arrOf (c3G L aw))).length == 181 &&
    (fixedList 693 (arrOf (j3G L aw * c3G L aw))).length == 21

@[expose] def commCheckG (aw kw : List (List ℤ)) : Bool :=
  let a1 := evalCodes (aGensG L aw) [2, 3]
  let k1 := evalCodes (kGensG L kw) [3]
  let a2 := evalCodes (aGensG L aw) [3, 6]
  let k2 := evalCodes (kGensG L kw) [1, 3, 1, 3, -1, 3, -1]
  commT 693 (toTable k1) (toTable (j1G L aw)) &&
    tblEq 693 (toTable (a1 * k1 * a1⁻¹ * k1⁻¹)) (toTable (j1G L aw)) &&
    commT 693 (toTable k2) (toTable (j2G L aw)) &&
    tblEq 693 (toTable (a2 * k2 * a2⁻¹ * k2⁻¹)) (toTable (j2G L aw))

@[expose] def orbitEltG (aw kw ow : List (List ℤ)) (i : ℕ) : Equiv.Perm (Fin 693) :=
  evalCodes (kGensG L kw) (ow.getD i []) * j1G L aw * (evalCodes (kGensG L kw) (ow.getD i []))⁻¹

@[expose] def transCheckG (aw kw ow sw : List (List ℤ)) : Bool :=
  (kGensG L kw ++ (kGensG L kw).map (·⁻¹)).all (fun g => (List.range 21).all fun i =>
      (List.range 21).any fun j =>
        tblEq 693 (toTable (g * orbitEltG L aw kw ow i * g⁻¹)) (toTable (orbitEltG L aw kw ow j))) &&
    (List.range 21).all fun m => m == 0 ||
      (commT 693 (toTable (evalCodes (kGensG L kw) (sw.getD m []))) (toTable (j1G L aw)) &&
        tblEq 693 (toTable (evalCodes (kGensG L kw) (sw.getD m []) * orbitEltG L aw kw ow 1 *
          (evalCodes (kGensG L kw) (sw.getD m []))⁻¹)) (toTable (orbitEltG L aw kw ow m)))

@[expose] def check3004G (aw : List (List ℤ)) (bt pts pos : Array ℕ) : Prop :=
  (aGensG L aw).all (fun g => (List.range 21).any fun i =>
      tblEq 693 (toTable g) (tvTabsG pts pos)[bt[i]!]!) = true ∧
    tblEq 693 (toTable (j1G L aw)) (tvTabsG pts pos)[bt[5]!]! = true

end CFSG.KC.U6

namespace CFSG.KC.U6

open CFSG.Sporadic.Th.Native CFSG.Fischer.Native

@[expose] def swapOKG (pts pos : Array ℕ) : Bool :=
  let T := tvTabsG pts pos
  (List.range 693).all fun p => (List.range 693).all fun q =>
    ap T[p]! q == q || ap T[p]! q == ap T[q]! p

@[expose] def fixOKG (fa : List ℕ) (pts pos : Array ℕ) : Bool :=
  let T := tvTabsG pts pos
  (List.range 693).all fun m => fa.contains m ||
    fa.any fun q => !(fa.contains (ap T[m]! q))

end CFSG.KC.U6

end
