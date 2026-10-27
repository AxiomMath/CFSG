module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public meta import CFSG.LargeExtraspecial.S63CD4Inputs

public section

namespace CFSG.LargeExtraspecial.A2Mod

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2.Native

@[expose] def conjProdWord (base : List ℕ) (cs : List (List ℕ)) : List ℕ :=
  cs.flatMap fun c => c ++ base ++ c.reverse

@[expose] def d4zConjs : List (List ℕ) :=
  [[], [7, 5, 7, 4, 2, 5, 7, 0, 3, 1], [0, 4, 7, 5, 1, 7, 0], [4, 7, 6, 7, 0, 3, 7, 1]]

@[expose] def d4tConjs : List (List ℕ) := [[], [3, 7, 3, 7, 5]]

@[expose] def order13R (x : Array ℕ) : Bool := powRows 24 x 13 == oneR && !(x == oneR)

@[expose] def d4SqueezeCheckZ : Bool :=
  gensOK d4Gens && order13R (wordR d4Gens (conjProdWord wordZ d4zConjs))

@[expose] def d4SqueezeCheckT : Bool :=
  gensOK d4Gens && order13R (wordR d4Gens (conjProdWord wordT d4tConjs))

end CFSG.LargeExtraspecial.A2Mod
