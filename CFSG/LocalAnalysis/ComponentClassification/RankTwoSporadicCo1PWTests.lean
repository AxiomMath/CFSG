module

public import Certificates.Data.CFSGNative.Co1Schreier.Base

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Co1

open CFSG.Sporadic.Co1Schreier.Native

@[expose] def commR (x y : Rows) : Bool := mul x y == mul y x

@[expose] def entryR (E : List Rows) (k : Nat) : Rows := E.getD (k - 1) one

@[expose] def conjProdR (E : List Rows) (z : Rows) (ps : List Nat) : Rows :=
  ps.foldl (fun acc k => mul acc (mul (mul (entryR E k) z) (inv (entryR E k)))) one

@[expose] def invsOK (E : List Rows) (ps : List Nat) : Bool :=
  ps.all fun k => mul (entryR E k) (inv (entryR E k)) == one

@[expose] def decOK (E : List Rows) (z : Rows) : List Rows → List (List Nat) → Bool
  | [], [] => true
  | s :: S, ps :: dec => invsOK E ps && conjProdR E z ps == s && decOK E z S dec
  | _, _ => false

@[expose] def pwCoreOK (E S : List Rows) (iz ih : Nat) (dec : List (List Nat)) (r : Rows) :
    Bool :=
  mul (mul (entryR E iz) (entryR E iz)) (mul (entryR E iz) (entryR E iz)) == one &&
    mul (entryR E ih) (entryR E iz) ==
      mul (mul (mul (entryR E iz) (entryR E iz)) (entryR E iz)) (entryR E ih) &&
    S.all (fun s => commR s r) && decOK E (mul (entryR E iz) (entryR E iz)) S dec

@[expose] def pwOK (S : List Rows) (d₂ : List (List Int)) (iz ih : Nat) (dec : List (List Nat))
    (r : Rows) : Bool :=
  (dag S d₂).2.2 && pwCoreOK (dag S d₂).1 S iz ih dec r

@[expose] def entriesR (base : List Rows) (d : List (List Int)) (idx : List Nat) : List Rows :=
  idx.map (entryR (dag base d).1)

@[expose] def wordsOK (B : List Rows) (d : List (List Int)) (idx : List Nat) (targets : List Rows) :
    Bool :=
  (dag B d).2.2 && entriesR B d idx == targets

end CFSG.ComponentClassification.RankTwoSporadic.Co1
