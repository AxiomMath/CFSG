module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23PerfInputs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi23PerfInputs

public section

namespace CFSG.EvenSporadicStandard.HypOne.Fi23

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.EvenSporadicStandard.Solomon78

@[expose] def kTxt : String := include_str "Fi23K.txt"

@[expose] def kLines : List String := kTxt.splitOn "\n"

@[expose] def kN : Nat := kLines[0]!.toNat!

@[expose] def kGens : List (List Nat) := ((kLines.drop 1).take kN).map parseWord

@[expose] def kPar : List Nat := parseWord kLines[kN + 1]!

@[expose] def kEven : List Nat := parseWord kLines[kN + 2]!

@[expose] def kWordD : List Nat := parseWord kLines[kN + 3]!

@[expose] def kWordE : List Nat := parseWord kLines[kN + 4]!

@[expose] def braidW (X Y : Array W) : Bool :=
  let P := mulW 253 X Y
  eqW 253 (mulW 253 P (mulW 253 P P)) (idW 253)

@[noinline, expose] def kCheckOf (g1 g2 : List Nat) (gs : List (List Nat))
    (par v wd we : List Nat) : Bool :=
  let D := matD
  let D1 := Solomon78.conjW g1
  let C := Solomon78.conjW g2
  let T : Array (Array W) := (gs.map Solomon78.conjW).toArray
  (g1 :: g2 :: gs).all (fun w => w.all fun x => decide (x < 2)) && decide (0 < gs.length) &&
    (v ++ wd ++ we).all (fun x => decide (x < gs.length)) &&
    (List.range gs.length).all (fun j => decide (j = 0) || decide (par.getD j 0 < j)) &&
    decide (v.length % 2 = 0) &&
    commW D D1 && commW D C && commW D1 C && canonW 253 D && canonW 253 D1 && canonW 253 C &&
    !eqW 253 D D1 && !eqW 253 D C && !eqW 253 D1 C &&
    (List.range gs.length).all (fun i => commW T[i]! D && commW T[i]! D1 && commW T[i]! C) &&
    (List.range gs.length).all (fun j => decide (j = 0) || braidW T[par.getD j 0]! T[j]!) &&
    eqW 253 (prodW 253 T [0]) (prodW 253 T v) &&
    eqW 253 D (prodW 253 T wd) && eqW 253 D1 (prodW 253 T we)

@[noinline, expose] def fi23KCheck : Bool :=
  kCheckOf fi23G1 fi23G2 kGens kPar kEven kWordD kWordE

end CFSG.EvenSporadicStandard.HypOne.Fi23
