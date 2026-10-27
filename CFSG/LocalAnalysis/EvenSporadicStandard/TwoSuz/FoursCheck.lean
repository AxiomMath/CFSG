module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.OuterCheck

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.SuzOddCore

@[expose] def foursWitnessText : String := include_str "FoursWords.txt"

@[expose] def foursWitnessLines : Array (List ℤ) :=
  ((foursWitnessText.splitOn "\n").filter fun l => l ≠ "").toArray.map outerParseWord

@[expose] def foursWitnessX : List ℤ := foursWitnessLines.getD 0 []

@[expose] def foursWitnessL (i : ℕ) : List ℤ := foursWitnessLines.getD (2 * i - 3) []

@[expose] def foursWitnessC (i : ℕ) : List ℤ := foursWitnessLines.getD (2 * i - 2) []

@[expose] def foursWordArr (w : List ℤ) : Array ℕ := wordArr 1782 #[b0Arr, b1Arr] w

@[expose] def foursWitnessPermOK (i : ℕ) : Bool :=
  eqA 1782 (compA 1782 (tArr i) (tArr i)) (idA 1782) &&
    eqA 1782
      (compA 1782 (compA 1782 (compA 1782 (foursWordArr (foursWitnessL i)) (tArr i))
        (foursWordArr (outerInvW (foursWitnessL i)))) (tArr i))
      (compA 1782 (compA 1782 (foursWordArr (foursWitnessC i)) (foursWordArr foursWitnessX))
        (foursWordArr (outerInvW (foursWitnessC i))))

@[noinline, expose] def foursWitnessCheck : Bool :=
  outerLvl0.valid && lettersOK 2 foursWitnessX && lettersOK 2 (foursWitnessL 2) &&
    lettersOK 2 (foursWitnessC 2) && lettersOK 2 (foursWitnessL 3) &&
    lettersOK 2 (foursWitnessC 3) &&
    mulM (outerLvl0.eval (foursWitnessX.map zCode)) (outerLvl0.eval (foursWitnessX.map zCode)) ==
      oneM &&
    !eqA 1782 (foursWordArr foursWitnessX) (idA 1782) &&
    foursWitnessPermOK 2 && foursWitnessPermOK 3

end CFSG.EvenSporadicStandard.TwoSuz
