module

public import CFSG.LargeExtraspecial.SMod20BasicCheck
public import Certificates.Data.SMod20RhoData

public section

namespace CFSG.SmithE

@[expose] def meetCard (i j : Nat) : Nat := (planePtsArr[i]!.filter (inPlane j)).size

@[expose] def distB (i j : Nat) : Nat :=
  let c := meetCard i j
  if c == 21 then 0 else if c == 5 then 1 else if c == 1 then 2 else 3

@[expose] def relB (R i j : Nat) : Bool := R.testBit (distB i j)

@[expose] def chkSpanW : Bool :=
  spanIdx.size == 20 && spanCoef.size == 20 && spanIdx.all (· < 891) &&
    (List.range 20).all fun m =>
      applyCols (spanIdx.map fun i => wtArr[i]!) spanCoef[m]! == 2 ^ m

@[expose] def chkDist : Bool :=
  (List.range 891).all fun i => (List.range 891).all fun j =>
    let c := meetCard i j
    (c == 0 || c == 1 || c == 5 || c == 21) && adjM i j == decide (distB i j ≤ 1)

@[expose] def rankOK (R : Nat) (rr cc inv : Array Nat) : Bool :=
  rr.size == 21 && cc.size == 21 && inv.size == 21 && rr.all (· < 891) && cc.all (· < 891) &&
    (List.range 21).all fun s => (List.range 21).all fun u =>
      (List.range 21).foldl (fun acc t => acc ^^ (relB R rr[s]! cc[t]! && inv[t]!.testBit u))
        false == (s == u)

@[expose] def chkRank : Bool :=
  rankRels == #[2, 4, 6, 10, 12, 14] && rankRows.size == 6 && rankCols.size == 6 &&
    rankInv.size == 6 &&
    (List.range 6).all fun r => rankOK rankRels[r]! rankRows[r]! rankCols[r]! rankInv[r]!

end CFSG.SmithE
