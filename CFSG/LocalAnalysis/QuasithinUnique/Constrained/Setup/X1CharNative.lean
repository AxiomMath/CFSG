module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def fullTables (n : Nat) (Ts : Array (List Nat)) : List (Array Nat) :=
  Ts.toList.map fun T => (T.take n).toArray

@[expose] def commIn (Z : List (Array Nat)) (x s : Array Nat) : Bool :=
  Z.any fun z => compArr x s == compArr z (compArr s x)

@[expose] def zStep (Rl gens Z : List (Array Nat)) : List (Array Nat) :=
  Rl.filter fun x => gens.all fun s => commIn Z x s

@[expose] def zSeries (Rl gens : List (Array Nat)) (idT : Array Nat) : Nat → List (Array Nat)
  | 0 => [idT]
  | k + 1 => zStep Rl gens (zSeries Rl gens idT k)

@[expose] def cenList (Rl Z : List (Array Nat)) : List (Array Nat) :=
  Rl.filter fun x => Z.all fun y => compArr x y == compArr y x

@[expose] def conjT (g gi q : Array Nat) : Array Nat := compArr g (compArr q gi)

@[expose] def normOK (L : List (Array Nat)) (g gi : Array Nat) : Bool :=
  L.all (fun q => L.contains (conjT g gi q)) && L.all (fun q => L.contains (conjT gi g q))

@[expose] def notNormOK (L : List (Array Nat)) (g gi : Array Nat) : Bool :=
  L.any fun q => !(L.contains (conjT g gi q))

@[expose] def invPairOK (idT g gi : Array Nat) : Bool :=
  compArr g gi == idT && compArr gi g == idT

end CFSG.QuasithinUnique.Setup.X1
