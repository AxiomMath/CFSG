module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYCheck
public import CFSG.Sporadic.SmallOddCore.J2CheckInputs
public import CFSG.Sporadic.SmallOddCore.J3CheckInputs

public section

namespace CFSG.EvenSporadicStandard.Fin76b.S16

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.SmallOddCore

@[expose] def f1Check (n : ℕ) (sift : Table → Bool) (τ0T ρT τT : Table) : Bool :=
  permOK n τ0T && permOK n ρT && permOK n τT && sift ρT && sift τT && commTT n ρT τ0T &&
  commTT n τT τ0T && tblEq n (powT n 8 ρT) (idT n) && !tblEq n (powT n 4 ρT) (idT n) &&
  invoOK n τT && invOK n ρT (invT n ρT) && tblEq n (compT n (compT n τT ρT) τT) (invT n ρT) &&
  (List.range 8).all fun i => !tblEq n τT (powT n i ρT)

@[expose] def j2F1OK : Bool := f1Check 315 j2Sift (j2CentTbl 9) (j2Tb 12) (j2Tb 13)

@[expose] def j3F1OK : Bool := f1Check 6156 j3Sift (j3CentTbl 21) (j3Tb 11) (j3Tb 12)

end CFSG.EvenSporadicStandard.Fin76b.S16
