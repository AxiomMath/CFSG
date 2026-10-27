module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8BridgeAux1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffE8_bridge (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {Ē : Subgroup (ProjSim Q)} {z ν : ProjSim Q}
    (h : FFE8SData hQ Ē z ν) :
    ∃ (E : Subgroup (OGroup Q)) (t ν' : OGroup Q), FFE8VData hQ E t ν' ∧
      Ē = E.map (ffSim Q) ∧ z = ffSim Q t ∧ ν = ffSim Q ν' :=
  ffOutFFE8Bridge_main hQ hdim hsgn h

end CFSG.OddStandard.SmallF3.Omega
