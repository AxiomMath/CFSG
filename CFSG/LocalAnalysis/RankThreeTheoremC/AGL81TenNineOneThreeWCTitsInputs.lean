module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsInputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
  CFSG.RankThree.PartTwo.Sec4.Item434RemTits

@[expose] def titsUWord : List ℤ := [2, -12, 4, 5, -11, -2]

@[expose] def titsUInvWord : List ℤ := [2, 11, -5, -4, 12, -2]

theorem yWord_eq : yWord = titsUWord ++ xWord ++ titsUInvWord := rfl

@[expose] def titsXArr : Array ℕ := wordArr 1755 titsDerivedArrs xWord

@[expose] def titsYArr : Array ℕ := wordArr 1755 titsDerivedArrs yWord

@[expose] def titsZArr : Array ℕ := wordArr 1755 titsDerivedArrs zWord

@[expose] def titsWCCheck : Bool :=
  lettersOK 13 xWord && lettersOK 13 yWord && lettersOK 13 zWord &&
    lettersOK 13 (titsUWord ++ titsUInvWord) &&
    eqA 1755 (wordArr 1755 titsDerivedArrs (titsUWord ++ titsUInvWord)) (idA 1755) &&
    sylArrs.all (fun g => !(commA g titsYArr && commA g titsZArr) || eqA 1755 g (idA 1755) ||
      eqA 1755 g titsXArr || eqA 1755 g (compA 1755 titsXArr titsXArr)) &&
    !(eqA 1755 titsYArr (idA 1755)) && !(eqA 1755 titsYArr titsXArr) &&
    !(eqA 1755 titsYArr (compA 1755 titsXArr titsXArr))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree
