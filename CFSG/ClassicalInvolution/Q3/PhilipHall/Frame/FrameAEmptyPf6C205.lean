module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf6Steps

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameSimple)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem mem_normalizer_Z_of_rho {ρ : G}
    (hρz : ρ * z * ρ⁻¹ = z * t) (hρt : ρ * t * ρ⁻¹ = z) :
    ρ ∈ Subgroup.normalizer ((Subgroup.closure ({t, z} : Set G) : Subgroup G) : Set G) := by
  apply Asc77.T3CII.mem_normalizer_of_conjSub_le
  unfold conjSub
  rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  intro x hx
  rw [SetLike.mem_coe, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rcases hx with h | h
  · rw [h, hρt]
    exact Subgroup.subset_closure (by simp)
  · rw [Set.mem_singleton_iff.mp h, hρz]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem frameH20_le_centralizer (d : Std20Frame K K' J S R R' W V z t) {a : G}
    (hA : a ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K')) :
    frameH20 (CoreAssembly.conjClass K) a R R' ≤ Subgroup.centralizer ({a} : Set G) := by
  have hR : ∀ r ∈ R, a * r = r * a := fun r hr =>
    commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd hA)
      hA.1 (Subgroup.mem_sup_left (d.hR.1 hr)) (d.hRS hr)
  have hR' : ∀ r ∈ R', a * r = r * a := fun r hr =>
    commutes_of_mem_centModOddCore S.isPGroup' (mem_centModOddCore_of_mem_centralizerModOdd hA)
      hA.1 (Subgroup.mem_sup_right (d.hR'.1 hr)) (d.hR'S hr)
  unfold frameH20
  refine sup_le (sup_le (iSup₂_le fun U hU => hU.2) ?_) ?_
  · exact fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hR r hr).symm
  · exact fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hR' r hr).symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
