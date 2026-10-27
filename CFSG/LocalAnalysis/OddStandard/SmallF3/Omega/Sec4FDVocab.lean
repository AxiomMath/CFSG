module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def Sec4FDDt (hQ : Q.Nondegenerate) (t : OGroup Q) :
    Subgroup (OGroup Q) :=
  omegaGroup hQ ⊓ Subgroup.centralizer ({t} : Set (OGroup Q))

theorem mem_sec4FDDt_iff (hQ : Q.Nondegenerate) {t u : OGroup Q} :
    u ∈ Sec4FDDt hQ t ↔ u ∈ omegaGroup hQ ∧ u * t = t * u := by
  rw [Sec4FDDt, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

end CFSG.OddStandard.SmallF3.Omega
