module

public import CFSG.Sporadic.Co1Block.TwoBCheckInputs

public section

namespace CFSG.EvenSporadicStandard.Co1Pair

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block

@[expose] def cpText : String := include_str "Co1PairTbl.txt"

@[expose] def cpNums : Array Nat :=
  ((cpText.splitOn " ").filterMap fun s => s.trimAscii.toNat?).toArray

@[expose] def cpReadWord (a : Array Nat) (p : Nat) : List Nat × Nat :=
  ((List.range a[p]!).map fun i => a[p + 1 + i]!, p + 1 + a[p]!)

@[expose] def cpReadWords (a : Array Nat) (m p : Nat) : Array (List Nat) × Nat := Id.run do
  let mut q := p
  let mut out : Array (List Nat) := #[]
  for _ in [0:m] do
    let r := cpReadWord a q
    out := out.push r.1
    q := r.2
  return (out, q)

@[expose] def cpN (i : Nat) : Nat := [1365, 1024, 180, 1, 1].getD i 1

@[expose] def cpF (i : Nat) : Nat := [0, 2, 4, 7].getD i 7

@[expose] def cpSsRead : Array (List Nat) × Nat := cpReadWords cpNums 5 6

@[expose] def cpTwRead0 : Array (List Nat) × Nat := cpReadWords cpNums (cpN 0) cpSsRead.2

@[expose] def cpTwRead1 : Array (List Nat) × Nat := cpReadWords cpNums (cpN 1) cpTwRead0.2

@[expose] def cpTwRead2 : Array (List Nat) × Nat := cpReadWords cpNums (cpN 2) cpTwRead1.2

@[expose] def cpTwRead (i : Nat) : Array (List Nat) × Nat :=
  match i with
  | 0 => cpTwRead0
  | 1 => cpTwRead1
  | _ => cpTwRead2

@[expose] def cpTw (i : Nat) : Array (List Nat) := (cpTwRead i).1

@[expose] def cpDec (i : Nat) : Array Nat :=
  let p := match i with
    | 0 => cpTwRead2.2
    | 1 => cpTwRead2.2 + cpN 0 * (7 - cpF 0)
    | _ => cpTwRead2.2 + cpN 0 * (7 - cpF 0) + cpN 1 * (7 - cpF 1)
  cpNums.extract p (p + cpN i * (7 - cpF i))

@[expose] def cpWord (gens : Array Rows) (w : List Nat) : Rows :=
  w.foldl (fun acc l => mul acc gens[l]!) one

@[expose] def cpX : Rows :=
  mul twoBXYRows.1 (pow (mul twoBXYRows.1 twoBXYRows.2) 13)

@[expose] def cpY : Rows := twoBXYRows.2

@[expose] def cpSs : Array Rows :=
  #[cpX, cpY] ++ cpSsRead.1.map (cpWord #[cpX, cpY])

@[expose] def cpTMs : Array (Array Rows) :=
  #[(cpTw 0).map (cpWord cpSs), (cpTw 1).map (cpWord cpSs), (cpTw 2).map (cpWord cpSs)]

@[expose] def cpTMget (i k : Nat) : Rows := if i < 3 then (cpTMs[i]!)[k]! else one

@[expose] def cpLevelOK (i : Nat) : Bool :=
  let tw := cpTw i
  let dec := cpDec i
  tw.size == cpN i && tw[0]! == [] &&
    tw.all (fun w => w.all fun l => decide (cpF i ≤ l) && decide (l < 7)) &&
    dec.size == cpN i * (7 - cpF i) &&
    (List.range (cpN i)).all fun k => (List.range (7 - cpF i)).all fun jj =>
      let p := dec[k * (7 - cpF i) + jj]!
      decide (p / cpN i / cpN (i + 1) < cpN (i + 2)) &&
        mul cpSs[cpF i + jj]! (cpTMget i k) ==
          mul (cpTMget i (p % cpN i))
            (mul (cpTMget (i + 1) (p / cpN i % cpN (i + 1)))
              (cpTMget (i + 2) (p / cpN i / cpN (i + 1))))

@[expose] def cpOK : Bool :=
  cpSsRead.1.size == 5 && cpSsRead.1.all (fun w => w.all (· < 2)) &&
    cpLevelOK 0 && cpLevelOK 1 && cpLevelOK 2

end CFSG.EvenSporadicStandard.Co1Pair
