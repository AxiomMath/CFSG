module

public import Mathlib.Data.List.Defs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TableX

@[expose] def innList (n : ℕ) (inn : ℕ → Bool) : List ℕ := (List.range n).filter inn

@[expose] def rootsIn (n : ℕ) (inn : ℕ → Bool) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : List ℕ :=
  (innList n inn).filter fun a => mul a a == tI

@[expose] def eListX (n : ℕ) (inn : ℕ → Bool) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : List ℕ :=
  let R := rootsIn n inn mul tI
  (0 :: R ++ R.flatMap (fun x => R.map (mul x))).dedup

@[expose] def rootsAll (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : List ℕ :=
  (List.range n).filter fun a => mul a a == tI

@[expose] def isNbr (mul : ℕ → ℕ → ℕ) (tI a b : ℕ) : Bool :=
  mul a b == mul b a || mul a b == mul (mul b a) tI

@[expose] def nbrCount (n : ℕ) (mul : ℕ → ℕ → ℕ) (tI a : ℕ) : ℕ :=
  ((rootsAll n mul tI).filter fun b => b != a && isNbr mul tI a b).length

end CFSG.EvenSporadicStandard.Fin76b.TableX
