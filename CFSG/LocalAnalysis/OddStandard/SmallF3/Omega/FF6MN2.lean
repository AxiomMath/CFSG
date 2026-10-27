module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_N2_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KN2 x) : LayerModel ↥(ffFix hQ (by omega) x) .PSU 3 1 := by
  obtain ⟨y, rfl, -, -, p, hp, rfl⟩ := hx
  rw [projOrthToProjSim_toProj]
  obtain ⟨hLie, hΩ, hπ, hcases⟩ := ff6m_N2_core hQ hdim hsgn hp
  have hfix : fixSub (simAct Q (orthToSim Q p)) = centralizer ({p} : Set (OGroup Q)) :=
    fixSub_simAct_orthToSim p
  have hCC : ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ≤
      centralizer ({p} : Set (OGroup Q)) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  refine ff6m_layerModel_of_twist hQ hdim (orthToSim Q p)
    ⁅centralizer ({p} : Set (OGroup Q)), centralizer ({p} : Set (OGroup Q))⁆ ?_ ?_ hLie ?_ hπ
  · rw [hfix]
    exact le_inf hΩ hCC
  · intro g hg h hh
    have h' := ff6mTwist_conj_mem_commutator (orthToSim Q p) hg (by rw [hfix]; exact hh)
    rwa [hfix] at h'
  · intro g hg
    rw [hfix] at hg
    rcases hcases g hg with h | h
    · exact mul_mem h h
    · have h2 := mul_mem h h
      have h3 : piOrth Q * g * (piOrth Q * g) = g * g :=
        calc piOrth Q * g * (piOrth Q * g) = piOrth Q * (g * piOrth Q) * g := by
              simp only [mul_assoc]
          _ = piOrth Q * (piOrth Q * g) * g := by rw [mul_piOrth_comm g]
          _ = (piOrth Q * piOrth Q) * (g * g) := by simp only [mul_assoc]
          _ = g * g := by rw [piOrth_mul_self, one_mul]
      rwa [h3] at h2

end CFSG.OddStandard.SmallF3.Omega
