module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3D8B

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement


open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Frame.late_R_le_cmo' (d : Std20Frame K K' J S R R' W V z t) :
    R ≤ centralizerModOdd (S : Subgroup G) K' := by
  intro x hx
  have hxK : x ∈ K := d.hR.1 hx
  rw [late_mem_cmo]
  refine ⟨d.hRS hx, d.late_K_le hxK,
    Disconnected.AschTight.mem_normalizer_oddCoreOf_of_mem_normalizer (d.late_K_le hxK),
    fun k hk => ?_⟩
  exact (Sec6Gen.comm_le_oddCore_of_twin d.late_hΩ d.late_mem_K d.late_mem_K' d.ne.symm
    d.viol.hzK d.late_hzK' (Subgroup.commutator_mem_commutator hxK hk)).2

theorem Std20Frame.late_20_8 (d : Std20Frame K K' J S R R' W V z t)
    (hc7 : centralizerModOdd (S : Subgroup G) (K ⊔ K') = Subgroup.zpowers z) :
    centralizerModOdd (S : Subgroup G) K' = R := by
  refine le_antisymm (fun x hx => ?_) d.late_R_le_cmo'
  obtain ⟨u₀, hu₀S, hu₀K⟩ := d.late_exists_swap
  obtain ⟨hu₀K', -, -, hu₀S'⟩ := d.late_swap_data hu₀S hu₀K
  have hy := late_cmo_conj_mem hx u₀⁻¹
  have hS1 : conjSub u₀⁻¹ (S : Subgroup G) = S := Sec7.conjSub_inv_eq hu₀S'
  have hK1 : conjSub u₀⁻¹ K' = K := by rw [← hu₀K, conjSub_inv_conjSub]
  rw [hS1, hK1] at hy
  have hyR' := d.late_stepA hc7 hy
  have hR : conjSub u₀ R' = R := by
    rw [d.late_R'_eq, late_conjSub_inf, hu₀K', hu₀S', ← d.late_R_eq]
  rw [← hR, mem_conjSub_iff]
  simpa using hyR'

end Std


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
