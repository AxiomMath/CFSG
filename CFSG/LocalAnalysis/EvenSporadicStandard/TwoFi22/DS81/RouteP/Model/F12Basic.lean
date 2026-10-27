module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.CentralFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F11Pin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Q0PlaneX

public section

open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem E0_le_Q0 :
    E0 ≤ Q0 := by
  intro g hg
  rw [mem_Q0_iff_of_fix]
  exact ⟨by simpa [planePt_zero] using E0_smul_planePt hg 0,
    by simpa [planePt_one] using E0_smul_planePt hg 1,
    by simpa [planePt_two] using E0_smul_planePt hg 2⟩

theorem E0_le_D0 :
    E0 ≤ D0 := by
  intro g hg
  rw [mem_D0_iff]
  exact ⟨E0_le_Q0 hg, E0_le_Zq hg⟩

theorem t0_mem_L0 :
    t0 ∈ L0 :=
  B0_le_L0 (E0_le_B0 t0_mem_E0)

theorem mul_comm_t0_of_mem_L0
    {r : Q3} (hr : r ∈ L0) :
    r * t0 = t0 * r := by
  let z : ↥L0 := ⟨t0, t0_mem_L0⟩
  have hz : z ∈ Subgroup.center ↥L0 := mem_center_L0_iff.2 (Or.inr rfl)
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨r, hr⟩)

theorem smul_planeX_eq_self_of_central
    {z : Q3} (hz : z ∈ E0) (hc : ∀ r ∈ Q0, r * z = z * r)
    (i : Fin 891) : z • planeX i = planeX i :=
  smul_eq_self_of_mem_orbit_of_forall_mul_comm hc (D0_smul_plane (E0_le_D0 hz))
    (planeX_mem_orbit i)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
