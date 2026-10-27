module

public import Certificates.Data.Smith1979W3.CensusData

public section

namespace CFSG.GF2Type.Smith1979W3.Cert690

@[expose] def censusBase (minus : Bool) (_ : Unit := ()) : Bool :=
  let D := grpData minus ()
  let Ld := ldata minus ()
  censusBaseOf minus D Ld

@[expose] def censusLWith (minus : Bool) (D : GrpData) (Ld : LData) (j : ℕ) : Bool :=
  let cands := candidatesOf minus Ld.Llist
  let CD := candData minus j ()
  sameSetA CD.L (Ld.Llist[cands[j]!]!) && censusLOf minus D CD

@[expose] def censusL (minus : Bool) (j : ℕ) (_ : Unit := ()) : Bool :=
  censusLWith minus (grpData minus ()) (ldata minus ()) j

@[expose] def censusCheck (minus : Bool) (_ : Unit := ()) : Bool :=
  let D := grpData minus ()
  let Ld := ldata minus ()
  let cands := candidatesOf minus Ld.Llist
  censusBaseOf minus D Ld &&
  (List.range cands.size).all fun ci => censusLWith minus D Ld ci

end CFSG.GF2Type.Smith1979W3.Cert690

end
