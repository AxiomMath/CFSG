module

public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.D42Tri

open CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def t2Perm : Equiv.Perm (Fin 360) := tp 360 (t2Tbl ())

@[expose] noncomputable def l0Gen (i : Fin 5) : Equiv.Perm (Fin 360) :=
  tp 360 (l0Tbls ()).toArray[i.val]!

@[expose] noncomputable def l0Sub : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure (Set.range l0Gen)

end CFSG.HardMathSupport.Dickson.Bal207.D42Tri
