module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.Chevalley

public noncomputable section

namespace CFSG.LocalAnalysis.GorensteinLyons

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

inductive ExceptionalRawTwoSpace
  | root (τ : Tag)
  | four

abbrev ExceptionalRawTwoGL (K : Type) [Field K] : ExceptionalRawTwoSpace → Type
  | .root τ => ModGL τ K
  | .four => Matrix.GeneralLinearGroup (Fin 4) K

instance instGroupExceptionalRawTwoGL (K : Type) [Field K] :
    (V : ExceptionalRawTwoSpace) → Group (ExceptionalRawTwoGL K V)
  | .root τ => inferInstanceAs (Group (ModGL τ K))
  | .four => inferInstanceAs (Group (Matrix.GeneralLinearGroup (Fin 4) K))

end CFSG.LocalAnalysis.GorensteinLyons
