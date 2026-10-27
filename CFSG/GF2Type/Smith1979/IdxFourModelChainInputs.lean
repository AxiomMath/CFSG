module

public import CFSG.GF2Type.Smith1979.GammaU.Bits
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.GF2Type.Smith1979.IdxFour.Chain

open CFSG.GF2Type.Smith1979.GammaU CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def permRows (r : Array ℕ) : Array ℕ := Array.ofFn (n := 4096) fun i => appN r i.val

@[expose] def chainStrong (gs : List (Array ℕ)) (ws : List (List ℤ)) : Array (Array ℕ) :=
  ws.foldl (fun S w => S.push (wordA 4096 S (S.map (invCand 4096)) w)) ((gs.map permRows).toArray)

@[expose] def chainWords (k : ℕ) (ws : List (List ℤ)) : Array (List ℤ) :=
  (List.replicate k [] ++ ws).toArray

@[expose] def chainBase (bl : List (Fin 4096)) : Array ℕ := (bl.map Fin.val).toArray

@[expose] def chainOK (gs : List (Array ℕ)) (ws : List (List ℤ)) (bl : List (Fin 4096))
    (N : ℕ) : Bool :=
  let S := chainStrong gs ws
  rawChainOK 4096 (S.extract 0 gs.length) S (chainBase bl) (chainWords gs.length ws) 4 &&
    (rawOrbitSizes 4096 S (chainBase bl)).prod == N

@[expose] def siftOK (gs : List (Array ℕ)) (ws : List (List ℤ)) (bl : List (Fin 4096))
    (yes no : List (Array ℕ)) : Bool :=
  let S := chainStrong gs ws
  let lv := rawLevels 4096 S (chainBase bl)
  (yes ++ no).all (fun r => r.size == 12 && r.all (· < 4096) &&
      isInvA 4096 (permRows r) (invCand 4096 (permRows r))) &&
    yes.all (fun r => siftA 4096 lv (chainBase bl) 0 (permRows r)) &&
    no.all (fun r => !siftA 4096 lv (chainBase bl) 0 (permRows r))

@[expose] def siftB (gs : List (Array ℕ)) (ws : List (List ℤ)) (bl : List (Fin 4096))
    (r : Array ℕ) : Bool :=
  r.size == 12 && r.all (· < 4096) && isInvA 4096 (permRows r) (invCand 4096 (permRows r)) &&
    siftA 4096 (rawLevels 4096 (chainStrong gs ws) (chainBase bl)) (chainBase bl) 0 (permRows r)

@[expose] def m0Words : List (List ℤ) :=
  [[2, -1, -2, 1, 2], [-2, -5, 2, 1, 2], [-5, 6, 5], [-4, 7, 4], [-7, 8, 7], [-3, -2, 4, 3, 4, 2]]

@[expose] def m0Base : List (Fin 4096) := [3, 192, 1, 4, 951, 311, 1151]

@[expose] def e0Words : List (List ℤ) :=
  [[-2, 1, 2], [-2, 4, 2], [-2, 5, 1], [-3, -6, -5, 3], [-5, -7, 5, 7], [-5, -3, 7, 3],
    [4, -8, 9, 8]]

@[expose] def e0Base : List (Fin 4096) := [12, 20, 264, 36, 63]

@[expose] def n0Words : List (List ℤ) :=
  [[-6, 7], [9, -6, -7, 9, 6], [-9, -9, 10, 9], [4, -10, 11, 10]]

@[expose] def n0Base : List (Fin 4096) := [1, 64, 2, 4, 951, 311, 1151]

@[expose] def saWords : List (List ℤ) :=
  [[-1, -1, 3, 1, 1], [-1, 4, 1], [-1, 5, 1], [-4, -5, 6, 5, 4], [-1, -7, -2, 1, 2],
    [-5, -7, -4, -6, 8, 6, 4]]

@[expose] def saBase : List (Fin 4096) := [960, 3, 48, 308, 543, 1021]

end CFSG.GF2Type.Smith1979.IdxFour.Chain
