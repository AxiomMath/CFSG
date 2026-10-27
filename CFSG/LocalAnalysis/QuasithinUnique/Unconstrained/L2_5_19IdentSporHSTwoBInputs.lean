module

public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.SmallOddCore.LocalCheck

public section

namespace CFSG.QuasithinUnique.Id2519.SporHS
open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

@[expose] def twoBGens : List Table := [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16]

@[expose] def twoBY : List Table :=
  [wordTbl 3850 twoBGens [4, 2, 1, 4], wordTbl 3850 twoBGens [3, 3]]

@[expose] def commOK (n cap : ℕ) (gs cs : List Table) : Bool :=
  let E := mulClosureH n gs.toArray cap
  cs.all fun c => cs.all fun c' =>
    memT n E.1 (compT n (compT n (compT n c c') (invT n c)) (invT n c'))

@[expose] def twoBCheck : Bool :=
  twoBGens.all (fun g => permOK 3850 g && invOK 3850 g (invT 3850 g)) &&
  twoBY.all (fun g => permOK 3850 g) && enumOK 3850 400 360 twoBY &&
  normOK 3850 400 twoBY twoBGens && commOK 3850 400 twoBY twoBGens

end CFSG.QuasithinUnique.Id2519.SporHS
