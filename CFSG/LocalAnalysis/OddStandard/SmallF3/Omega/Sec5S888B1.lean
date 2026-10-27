module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End1b

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem isPlanes_of_setup [Finite H] (hS : PlaneSetup z K α) :
    IsPlanes (planeV hS.quad α) (planeW hS.quad α) := by
  haveI : Finite X := Finite.of_surjective α hS.surj
  refine ⟨planeV_comm hS.quad α hS.ker, planeV_sq hS.quad α hS.ker, ?_, planeW_le hS.quad α,
    card_planeW hS, planeV_decomp hS.quad α⟩
  exact card_V_of_planes (planeV_comm hS.quad α hS.ker) (planeW_le hS.quad α)
    (card_planeW hS) (planeV_decomp hS.quad α) (planeRho_mem hS.quad α)
    (planeRho_inv hS.quad α) (planeRho_triv hS.quad α) (planeRho_fpf hS.quad α hS.ker)

theorem planeSys_of_setup [Finite H] (hS : PlaneSetup z K α)
    (hperm : ∀ x ∈ normalizer (Sec5B517Q8 hS.quad : Set H), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (K i) x = K j) :
    PlaneSys (planeV hS.quad α) (planeW hS.quad α) := by
  refine ⟨isPlanes_of_setup hS, ?_⟩
  intro g hg i
  obtain ⟨x, rfl⟩ := hS.surj g
  have hxN : x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) :=
    (mem_normalizer_planeV_iff hS).mp hg
  obtain ⟨j, hj⟩ := hperm x⁻¹ (inv_mem hxN) i
  refine ⟨j, ?_⟩
  intro w hw
  rw [planeW, Subgroup.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨huQ, huK⟩ := Subgroup.mem_inf.mp hu
  refine Subgroup.mem_map.mpr ⟨x * u * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_inf]
    constructor
    · exact (Subgroup.mem_set_normalizer_iff.mp hxN u).mp huQ
    · have hmem : x * u * x⁻¹ ∈ CFSG.conjugate (K i) x⁻¹ := by
        rw [CFSG.conjugate, Subgroup.mem_map]
        exact ⟨u, huK, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rwa [hj] at hmem
  · simp only [map_mul, map_inv, inv_inv]

end CFSG.OddStandard.SmallF3.Omega
