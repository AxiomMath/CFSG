module

public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix

@[expose] noncomputable def e8M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  toMat Tag.E8.rank e8FourMat

end CFSG.HardMathSupport.Timmesfeld.CrossChar
