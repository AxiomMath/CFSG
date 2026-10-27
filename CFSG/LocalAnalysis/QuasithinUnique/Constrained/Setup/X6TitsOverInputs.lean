module

public import CFSG.Sporadic.Schreier.TitsData

public section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat

open CFSG.Sporadic.Schreier.Tits

@[expose] def titsInvWord (w : List Int) : List Int := (w.map Neg.neg).reverse

@[expose] def titsFlagRepWords : List (List Int) :=
  [[4, -1, 3, 1], [2, 4, 2, -13, 2], [-1, -10, 1], [13, 1, 10, -1], [13, 4, 1], [13, -1],
    [7, 6, -2], [3, -11, 3, -1], [8, 4, 2], [1, 1, -4, -2], [-7, -2, 13, 2], [4, 2, 6, -1],
    [13, 5, -1, -2, -1], [7, 3, -2, 1], [13, 4, 1, 1]]

@[expose] def titsFlagZLetters : List (List Nat) :=
  [[3, 0, 4], [4, 0, 3], [4, 0, 0, 3, 2, 3, 2, 4, 0, 0, 3], [4, 1, 3], [3, 2, 2, 4], [4, 2, 2, 3],
    [3, 1, 2, 4, 4, 1, 3], [4, 2, 2, 3], [3, 0, 0, 0, 0, 4], [4, 0, 0, 0, 0, 3],
    [3, 1, 3, 1, 0, 0, 3], [3, 0, 1, 1, 3, 0, 3], [4, 0, 1, 2, 0, 2, 3], [4, 1, 0, 3, 0, 2, 3],
    [3, 3, 2, 4, 0, 3]]

@[expose] def titsFlagRepWord (l : Nat) : List Int := titsFlagRepWords.getD l []

@[expose] def titsFlagPiece (g : List Int) (c : Nat) : List Int :=
  if c < 3 then titsSWords.getD c [] else if c = 3 then g else titsInvWord g

@[expose] def titsFlagZWord (l : Nat) : List Int :=
  (titsFlagZLetters.getD l []).flatMap (titsFlagPiece (titsFlagRepWord l))

end CFSG.QuasithinUnique.Setup.X6.TitsLat
