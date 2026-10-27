module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEMod1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fk_fr_exists_lift_omega (hQ : Q.Nondegenerate) {z : ProjSim Q}
    (hz : SimInOmegaStar hQ z) : ∃ g ∈ omegaGroup hQ, phiSim Q g = z := by
  obtain ⟨y, hy, hyz⟩ := hz
  obtain ⟨g, hg, hgy⟩ := (mem_omegaProj_iff hQ).mp hy
  refine ⟨g, hg, ?_⟩
  show projOrthToProjSim Q (toProj Q g) = z
  rw [hgy, hyz]

theorem fk_fr_mem_omega_of_simInOmegaStar (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {h : OGroup Q}
    (hh : SimInOmegaStar hQ (phiSim Q h)) : h ∈ omegaGroup hQ := by
  obtain ⟨g, hg, hgphi⟩ := fk_fr_exists_lift_omega hQ hh
  have hker : phiSim Q (g⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, hgphi, inv_mul_cancel]
  rcases phiSim_eq_one_iff.mp hker with hgh | hgp
  · have hh1 : h = g := (inv_mul_eq_one.mp hgh).symm
    rw [hh1]
    exact hg
  · have hh2 : h = g * piOrth Q := inv_mul_eq_iff_eq_mul.mp hgp
    rw [hh2]
    exact (omegaGroup hQ).mul_mem hg (ff6m_piOrth_mem_omega hQ hdim hsgn)

end CFSG.OddStandard.SmallF3.Omega
