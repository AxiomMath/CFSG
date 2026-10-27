module


public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import CFSG.GroupTheory.PGroup.NormalTwoCentralInvolutionContainment

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddDimCentralInvolutionForcesAbelian

theorem abelian {H F W : Type*} [Group H] [Finite H] [Field F] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (hH2 : IsPGroup 2 H) (h2 : (2 : F) ≠ 0)
    (σ : Representation F H W) (z : H) (hz : z ∈ Subgroup.center H) (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1)
    (huniq : ∀ y ∈ Subgroup.center H, y ^ 2 = 1 → y ≠ 1 → y = z)
    (hzneg : σ z = -LinearMap.id) (hdim : Odd (Module.finrank F W)) :
    IsMulCommutative H := by
  by_contra hnc
  have hne : commutator H ≠ ⊥ := fun h => hnc ((commutator_eq_bot_iff H).mp h)
  have hzmem : z ∈ commutator H :=
    NormalTwoCentralInvolutionContainment.mem hH2 z hz hz2 hz1 huniq (commutator H) hne
  let f : H →* Fˣ := ((LinearMap.det : (W →ₗ[F] W) →* F).comp σ).toHomUnits
  have hker := Abelianization.commutator_subset_ker f hzmem
  have h1 : ((LinearMap.det : (W →ₗ[F] W) →* F).comp σ) z = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hker)
    simpa [f] using this
  simp only [MonoidHom.comp_apply, hzneg] at h1
  have h3 : LinearMap.det (-(LinearMap.id : W →ₗ[F] W)) = (-1) ^ Module.finrank F W := by
    have := LinearMap.det_smul (-1 : F) (LinearMap.id : W →ₗ[F] W)
    simpa using this
  have h4 : LinearMap.det (-(LinearMap.id : W →ₗ[F] W)) = -1 := by
    rw [h3, hdim.neg_one_pow]
  rw [h4] at h1
  apply h2
  linear_combination -h1

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddDimCentralInvolutionForcesAbelian
