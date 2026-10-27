module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4Pi
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MTwist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6m_K4_layerModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx2 : x * x = 1) (hx : KM4 x) :
    LayerModel ↥(ffFix hQ (by omega) x) .PSL 2 2 := by
  obtain ⟨ρ, rfl, hρ, hρρ⟩ := ff6m_K4_split hQ hdim hsgn hx2 hx
  obtain ⟨hLie, hle, hsq⟩ := ff6m_K4_core hQ hdim hρ hρρ
  have hC : ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆ ≤ fixSub (simAct Q ρ) := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp hq) (inv_mem hp)) (inv_mem hq)
  exact ff6m_layerModel_of_twist hQ hdim ρ ⁅fixSub (simAct Q ρ), fixSub (simAct Q ρ)⁆
    (le_inf hle hC) (fun g hg h hh => ff6mTwist_conj_mem_commutator ρ hg hh) hLie
    (fun g hg => hsq g (mem_fixSub_iff.mp (Subgroup.mem_inf.mp hg).2))
    (ff6m_K4_pi_not_mem hQ hdim hρ hρρ)

end CFSG.OddStandard.SmallF3.Omega
