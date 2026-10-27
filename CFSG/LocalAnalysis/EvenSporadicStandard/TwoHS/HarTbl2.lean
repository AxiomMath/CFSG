module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarTbl

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Recognition.HSMultiplier

@[expose] def conjOK (n : ℕ) (sift : Table → Bool) (c r x : Table) : Bool :=
  permOK n c && invOK n c (invT n c) && sift c && tblEq n (conjT n c (invT n c) r) x

@[expose] def harConjHex : String := include_str "HarModelConj.txt"

@[expose] def harConj (j : ℕ) : Table := hexT 3 3850 (3850 * j) harConjHex

@[expose] def harLiftOK : Bool :=
  harU.all (permOK 11200) && harUX.all (permOK 3850) && !tblEq 11200 harC0 (idT 11200) &&
  conjOK 3850 hsSift (harConj 0) (hsCentTbl 5) (tUX [3, 3, 3, 3]) &&
  conjOK 3850 hsSift (harConj 1) (hsCentTbl 12) (tUX [1, 2, 1, 2, 3]) &&
  tblEq 11200 (compT 11200 (tU [1, 2, 1, 2, 3]) (tU [1, 2, 1, 2, 3])) harC0 &&
  tblEq 3850 (tUX [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (idT 3850)

@[expose] def harSPairs : List (List ℕ × List ℕ) :=
  [([1, 3, 1, 2, 4], [1, 1, 1, 4, 1, 4]), ([1, 1, 1, 3, 1, 2, 4], [1, 2, 1, 1, 3, 4]),
    ([1, 3, 2, 4, 2, 4, 3], [1, 1, 1, 1, 1, 4]), ([1, 4, 1, 3, 2, 1], [3, 3, 4, 4, 4])]

@[expose] def harSCgens : List Table :=
  harSPairs.map fun p =>
    tComm 3850 (wordTbl 3850 hsSylowGenTbls p.1) (wordTbl 3850 hsSylowGenTbls p.2)

@[expose] def harSOK : Bool :=
  let n := 3850
  let C := (mulClosureH n harSCgens.toArray 200).1
  hsSylowGenTbls.all (fun g => permOK n g && invOK n g (invT n g)) &&
  harSPairs.all (fun p => hsSift (wordTbl n hsSylowGenTbls p.1) &&
    hsSift (wordTbl n hsSylowGenTbls p.2)) &&
  harSCgens.all (permOK n) && enumOK n 200 64 harSCgens &&
  normOK n 200 harSCgens hsSylowGenTbls &&
  hsSylowGenTbls.all (fun g => hsSylowGenTbls.all fun h => memT n C (tComm n g h))

@[expose] def harRHex : String := include_str "HarRTbl.txt"

@[expose] def harRT (c j : ℕ) : Table := hexT 3 3850 (3850 * (7 * c + j)) harRHex

@[expose] def harRho (c : ℕ) : Table := hsCentTbl (21 + 13 * c)

@[expose] def harBPairs (c : ℕ) : List (List ℕ × List ℕ) :=
  if c = 0 then
    [([2, 1, 2, 2, 1, 2, 1, 2, 2], [2, 2, 1, 2, 1, 2, 2, 1, 2]),
      ([2, 2], [1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1])]
  else [([2, 1, 2, 2, 2], [1, 2, 2, 2, 1, 2]), ([1, 2, 1], [1, 2, 2])]

@[expose] def harFourOK (c : ℕ) : Bool :=
  let n := 3850
  let ρ := harRho c
  let B := [harRT c 3, harRT c 4]
  permOK n ρ && invOK n ρ (invT n ρ) &&
  conjOK n hsSift (harRT c 1) (hsCentTbl 12) (harRT c 0) && commTT n (harRT c 0) ρ &&
  conjOK n hsSift (harRT c 2) ρ (compT n (harRT c 0) ρ) &&
  B.all (fun g => permOK n g && invOK n g (invT n g) && hsSift g && commTT n g ρ) &&
  (harBPairs c).length == 2 &&
  tblEq n (tComm n (wordTbl n B ((harBPairs c).getD 0 ([], [])).1)
    (wordTbl n B ((harBPairs c).getD 0 ([], [])).2)) (harRT c 3) &&
  tblEq n (tComm n (wordTbl n B ((harBPairs c).getD 1 ([], [])).1)
    (wordTbl n B ((harBPairs c).getD 1 ([], [])).2)) (harRT c 4) &&
  conjOK n hsSift (harRT c 5) (hsCentTbl 5) (harRT c 3) &&
  conjOK n hsSift (harRT c 6) ρ (compT n ρ (harRT c 3))

end CFSG.EvenSporadicStandard.TwoHS
