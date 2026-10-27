module

public import CFSG.LargeExtraspecial.S63CD4Inputs
public meta import CFSG.LargeExtraspecial.S63CD4Inputs

public section

namespace CFSG.LargeExtraspecial.S63

@[expose] def d4yWord : List ℕ := [3, 2, 4]

@[expose] def d4yInvWord : List ℕ := [4, 2, 3]

@[expose] def d4MidQWord : List ℕ := [7, 0, 5, 0]

@[expose] def d4SplitCheck : Bool :=
  mulR (wordR d4Gens d4yWord) (wordR d4Gens d4yInvWord) == oneR &&
  mulR d4Gens[0]! z0R == mulR z0R d4Gens[0]! &&
  mulR (wordR d4Gens d4yWord) z0R == mulR z0R (wordR d4Gens d4yWord) &&
  mulR d4Gens[0]! d4Gens[1]! == mulR d4Gens[1]! d4Gens[0]! &&
  mulR d4Gens[0]! d4Gens[2]! == mulR d4Gens[2]! d4Gens[0]! &&
  mulR d4Gens[1]! d4Gens[2]! == mulR d4Gens[2]! d4Gens[1]! &&
  mulR (mulR (wordR d4Gens d4yWord) d4Gens[0]!) (wordR d4Gens d4yInvWord) == d4Gens[2]! &&
  mulR (mulR (wordR d4Gens d4yWord) d4Gens[2]!) (wordR d4Gens d4yInvWord) ==
    mulR d4Gens[2]! d4Gens[1]! &&
  mulR (mulR (wordR d4Gens d4yWord) (mulR d4Gens[2]! d4Gens[1]!)) (wordR d4Gens d4yInvWord) ==
    mulR d4Gens[2]! d4Gens[0]! &&
  wordR qGens d4MidQWord == d4Gens[6]!

end CFSG.LargeExtraspecial.S63
