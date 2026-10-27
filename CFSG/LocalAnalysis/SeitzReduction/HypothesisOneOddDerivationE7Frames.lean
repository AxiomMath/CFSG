module

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.SeitzReduction

open CFSG.Blueprint.Chevalley

@[expose] def oddDerivE7YFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 2, 3, 3, 2, 1], ![1, 2, 2, 3, 2, 2, 1]]

@[expose] def oddDerivE7ZFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0], ![1, 1, 2, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1, 1]]

@[expose] def oddDerivE7UFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 1, 1, 1], ![0, 1, 1, 2, 2, 2, 1]]

@[expose] def oddDerivE7VFrame : List (Fin Tag.E7.rank → ℤ) :=
  [![1, 2, 2, 3, 2, 1, 0], ![0, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 1, 1]]

end CFSG.SeitzReduction
