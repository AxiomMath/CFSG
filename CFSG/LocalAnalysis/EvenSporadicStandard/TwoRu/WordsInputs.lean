module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs
public import Certificates.Data.CFSGNative.Schreier.SetOrbit

public section

namespace CFSG.EvenSporadicStandard.TwoRu

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.Recognition.RuMultiplier CFSG.LieType.Multipliers.Tits

@[expose] def ruFourthW1 : List (Fin gc × Bool) := ruW [5, 2]

@[expose] def ruFourthW2 : List (Fin gc × Bool) :=
  ruW ([3, 1, 5, 1, 5, 1, 4] ++ [3, 1, 5, 1, 5, 1, 4])

@[expose] def wordPow (k : ℕ) (w : List (Fin gc × Bool)) : List (Fin gc × Bool) :=
  (List.replicate k w).flatten

@[expose] def ruZWord : List (Fin gc × Bool) := ruP0 ++ ruP0

@[expose] def ruFix16240 (t : Array ℕ) : ℕ := (fixedList 16240 t).length

@[expose] def ruWordArr (w : List (Fin gc × Bool)) : Array ℕ := wordArr 16240 ruRhoArrs (zword w)

@[expose] def ruFourthOne (w : List (Fin gc × Bool)) (n : ℕ) : Bool :=
  lettersOK gc (zword (wordPow 8 w)) && lettersOK gc (zword (wordPow 4 w)) &&
    eqA 16240 (ruWordArr (wordPow 8 w)) (idA 16240) &&
    !eqA 16240 (ruWordArr (wordPow 4 w)) (idA 16240) &&
    !eqA 16240 (ruWordArr (wordPow 4 w)) (ruWordArr ruZWord) &&
    (ruFix16240 (ruWordArr (wordPow 4 w)) == n)

@[noinline, expose] def ruFourthCheck : Bool :=
  lettersOK gc (zword ruZWord) && !eqA 16240 (ruWordArr ruZWord) (idA 16240) &&
    ruFourthOne ruFourthW1 320 && ruFourthOne ruFourthW2 48

end CFSG.EvenSporadicStandard.TwoRu
