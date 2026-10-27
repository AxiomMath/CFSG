module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Mat
public import CFSG.Sporadic.Recognition.SuzMultiplierInputs

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open CFSG.Sporadic.Recognition.SuzMultiplier (suzCover suzR3 gcS)
open CFSG.Sporadic.Bridge.SuzGPL.Native (surjWords)

@[expose] def coverGenText : String := include_str "CoverGen.txt"

@[expose] def parseMats (s : String) : Array Mt :=
  let ls := (s.splitOn "\n").filter fun l => l ≠ ""
  (Array.range (ls.length / 12)).map fun k =>
    ((ls.drop (12 * k)).take 12).foldl
      (fun acc l => acc ++ (l.toList.map fun c => c.toNat - 48).toArray) #[]

@[expose] def coverMats : Array Mt := parseMats coverGenText

@[expose] def powM (A : Mt) : ℕ → Mt
  | 0 => oneM
  | n + 1 => mulM (powM A n) A

@[expose] def invM (A : Mt) : Mt :=
  ((List.range 24).find? fun k => powM A (k + 1) == oneM).elim oneM fun k => powM A k

@[expose] def negM : Mt :=
  Array.ofFn (n := 144) fun p => if p.val / 12 = p.val % 12 then 2 else 0

@[expose] def coverGS : GenSys :=
  ⟨coverMats.extract 0 7, (coverMats.extract 0 7).map invM⟩

@[expose] def matA : Mt := coverMats.getD 7 oneM

@[expose] def matB : Mt := coverMats.getD 8 oneM

@[expose] def zCode (z : ℤ) : ℕ :=
  if 0 < z then 2 * (z - 1).toNat else 2 * (-z - 1).toNat + 1

@[expose] def wordCodes (w : List (Fin gcS × Bool)) : List ℕ :=
  w.map fun l => 2 * l.1.val + if l.2 then 0 else 1

@[noinline, expose] def coverCheck : Bool :=
  coverMats.size == 9 && coverGS.valid &&
    (List.range 9).all (fun i => canonB (coverMats.getD i oneM)) &&
    suzCover.all (fun w => coverGS.eval (wordCodes w) == oneM) &&
    coverGS.eval (wordCodes suzR3) == oneM &&
    coverGS.eval [6, 6] == negM &&
    mulM negM matA == coverGS.eval ((surjWords.getD 0 []).map zCode) &&
    mulM negM matB == coverGS.eval ((surjWords.getD 1 []).map zCode)

end CFSG.EvenSporadicStandard.TwoSuz
