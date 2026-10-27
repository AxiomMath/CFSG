module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimLine
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimScalar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimSpan

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffSimOmegaAct_injective (hQ : Q.Nondegenerate)
    (h5 : 5 ≤ Module.finrank (ZMod 3) V) :
    Function.Injective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* MulAut (omegaProj hQ)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have hγ := (ffSimOmegaAct_eq_one_iff hQ (by omega) γ).mp hx
  obtain ⟨c, hc⟩ := ff_eigen_const hQ (by omega) (γ : V ≃ₗ[ZMod 3] V)
    (fun u hu => ff_simAct_line hQ h5 γ hγ hu)
  exact ff_mk_eq_one_of_smul (by omega) γ (ff_eq_smul_of_eigen hQ hc)

end CFSG.OddStandard.SmallF3.Omega
