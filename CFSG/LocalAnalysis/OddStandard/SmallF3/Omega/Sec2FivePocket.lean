module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem omegaToProj_injective_of_not_mem (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) : Function.Injective (omegaToProj hQ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rcases (omegaToProj_eq_one_iff hQ g).mp hg with h | h
  · exact Subtype.ext h
  · exfalso
    apply hπ
    rw [← h]
    exact g.2

@[expose] noncomputable def omegaProjEquiv (hQ : Q.Nondegenerate)
    (hπ : piOrth Q ∉ omegaGroup hQ) : omegaGroup hQ ≃* omegaProj hQ :=
  MulEquiv.ofBijective (omegaToProj hQ)
    ⟨omegaToProj_injective_of_not_mem hQ hπ, omegaToProj_surjective hQ⟩

end CFSG.OddStandard.SmallF3.Omega
