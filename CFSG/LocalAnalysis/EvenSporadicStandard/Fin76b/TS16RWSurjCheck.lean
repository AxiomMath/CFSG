module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWSurjData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWClsCheck

public section

namespace CFSG.EvenSporadicStandard.Fin76b.W16

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

@[expose] def inH1 (g : Array Nat) : Bool := g[32]! == 32 || g[32]! == 53

@[expose] def omegaClosed : Bool :=
  decide (omegaSets.size = 216) &&
  (List.range 216).all (fun j => decide (omegaSets[j]!.size = 8) &&
      omegaSets[j]!.all fun x => decide (x < 128)) &&
  sameSet omegaSets[0]! #[0, 21, 32, 53, 64, 85, 96, 117] &&
  (List.range 36).all fun gi => (List.range 216).all fun j =>
    (List.range 216).any fun j' => sameSet (imgSet sgsArr[gi]! omegaSets[j]!) omegaSets[j']!

@[expose] def g0Check : Bool :=
  decide (g0Gens.size = 3) &&
  (List.range 3).all (fun k => decide (g0Gens[k]!.size = 128) &&
      isInvA 128 g0Gens[k]! (invCand 128 g0Gens[k]!) && inPg g0Gens[k]! &&
      sameSet (imgSet g0Gens[k]! omegaSets[0]!) omegaSets[0]!) &&
  decide (g0Par.size = 216) &&
  (List.range 216).all (fun j =>
    g0Par[j]!.1 == j ||
      (decide (g0Par[j]!.1 < j) && decide (g0Par[j]!.2 < 3) &&
        sameSet (imgSet g0Gens[g0Par[j]!.2]! omegaSets[g0Par[j]!.1]!) omegaSets[j]!)) &&
  (List.range 216).all (fun j => g0Par[j]!.1 != j || rootsArr.contains j)

@[expose] def treeOK (r : Nat) : Bool :=
  let gens := g0Gens.push gamReps[r]!
  let T := treeData[r]!
  decide (T.size = 216) && (T[0]! == #[0, 0, 0]) &&
  (List.range 215).all (fun k' =>
    let k := k' + 1
    let row := T[k]!
    decide (row.size = 3) && decide (row[1]! < k) && decide (row[2]! < 4) &&
      decide (row[0]! < 216) && decide ((T[row[1]!]!)[0]! < 216) &&
      sameSet (imgSet gens[row[2]!]! omegaSets[(T[row[1]!]!)[0]!]!) omegaSets[row[0]!]!) &&
  (List.range 216).all fun j => (List.range 216).any fun k => (T[k]!)[0]! == j

@[expose] def rootCheck (r : Nat) : Bool :=
  decide (gamReps[r]!.size = 128) && isInvA 128 gamReps[r]! (invCand 128 gamReps[r]!) &&
  inPg gamReps[r]! && decide (rootsArr[r]! < 216) &&
  sameSet (imgSet gamReps[r]! omegaSets[0]!) omegaSets[rootsArr[r]!]! &&
  (inH1 gamReps[r]! || treeOK r)

@[expose] def surjCheck : Bool :=
  omegaClosed && g0Check && decide (rootsArr.size = 10) && decide (gamReps.size = 10) &&
    decide (treeData.size = 10) && (List.range 10).all rootCheck

end CFSG.EvenSporadicStandard.Fin76b.W16
