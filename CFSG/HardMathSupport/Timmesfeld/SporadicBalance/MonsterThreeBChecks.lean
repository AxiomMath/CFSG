module

public import Certificates.Data.CFSGNative.Timmesfeld.M3B

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF

open _root_.Timmesfeld.M3B (AD B0 LA Da Db repD tD cubeE zconjE eOf adPow zeroV)

@[expose] def letterInvCheck (_ : Unit := ()) : Bool :=
  _root_.Timmesfeld.M3B.adEq (_root_.Timmesfeld.M3B.comp (B0 ())
    ((LA ()).getD 2 _root_.Timmesfeld.M3B.adOne) (Da ())) _root_.Timmesfeld.M3B.adOne &&
  _root_.Timmesfeld.M3B.adEq (_root_.Timmesfeld.M3B.comp (B0 ())
    ((LA ()).getD 3 _root_.Timmesfeld.M3B.adOne) (Db ())) _root_.Timmesfeld.M3B.adOne

@[expose] def tDk (k : Nat) : AD := if k = 0 then _root_.Timmesfeld.M3B.adOne else tD k

@[expose] def rootClaims : List (Nat × List Nat × Nat × List Nat) :=
  [(0, [0,0,0,0,0,0,0,0,0,0,0,0], 4, []),
    (0, [0,1,0,0,0,0,0,0,0,0,0,0], 3, [1]),
    (0, [1,0,0,0,0,0,0,0,0,0,0,0], 3, [0,2]),
    (1, [0,0,0,0,0,0,0,0,0,0,0,0], 2, []),
    (1, [0,0,0,1,0,0,0,0,0,0,0,0], 3, [2,1,0,2,0,0,2,0,0,0,0,0]),
    (1, [1,0,0,0,0,0,0,0,0,0,0,0], 1, []),
    (2, [0,0,0,0,0,0,0,0,0,0,0,0], 2, []),
    (2, [1,0,0,0,0,0,0,0,0,0,0,0], 0, []),
    (3, [0,0,0,0,0,0,0,0,0,0,0,0], 2, []),
    (3, [1,0,0,0,0,0,0,0,0,0,0,0], 0, []),
    (3, [0,0,0,0,0,1,0,0,0,0,0,0], 0, []),
    (3, [0,0,0,0,0,0,0,0,0,0,0,1], 3, [0,2,2,2,2,2,0,0,0,0,0,0]),
    (3, [1,1,0,0,0,0,0,0,0,0,0,0], 1, []),
    (3, [0,1,0,1,0,0,0,0,0,0,0,0], 3, [0,0,0,0,0,0,0,0,0,0,0,1])]

@[expose] def rootOK (c : Nat × List Nat × Nat × List Nat) : Bool :=
  let B := B0 ()
  let D := repD c.1 c.2.1
  let x := eOf c.2.1 0
  let t := tDk c.1
  let cu := cubeE B t x
  if c.2.2.1 = 0 then !_root_.Timmesfeld.M3B.adEq (adPow B D 3) _root_.Timmesfeld.M3B.adOne
  else if c.2.2.1 = 4 then _root_.Timmesfeld.M3B.adEq D _root_.Timmesfeld.M3B.adOne
  else !_root_.Timmesfeld.M3B.adEq D _root_.Timmesfeld.M3B.adOne &&
    (if c.2.2.1 = 1 then _root_.Timmesfeld.M3B.eeq (zeroV, cu.2) cu && cu.2 != 0
      else _root_.Timmesfeld.M3B.eeq cu _root_.Timmesfeld.M3B.eone) &&
    (c.2.2.1 != 3 || _root_.Timmesfeld.M3B.eeq (zconjE B t x (eOf c.2.2.2 0))
      (_root_.Timmesfeld.M3B.emul B x (zeroV, 1)))

@[expose] def rootsOK (_ : Unit := ()) : Bool := rootClaims.all rootOK

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
