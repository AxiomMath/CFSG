module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSDef
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFThetaSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def ffP1Sim (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup (ProjSim Q) :=
  (ffP1p hQ fr).map (ffOmegaToSim hQ)

@[expose] noncomputable def ffB1Sim (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup (ProjSim Q) :=
  (ffB1p hQ fr).map (ffOmegaToSim hQ)

@[expose] noncomputable def ffZ0Sim (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ProjSim Q :=
  ffOmegaToSim hQ (ffZ0s hQ fr)

end CFSG.OddStandard.SmallF3.Omega
