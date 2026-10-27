module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI

variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

theorem strong_embedding_preimage_of_odd_kernel (f : G →* K)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (Y : Subgroup K) (hY : IsStronglyEmbedded Y) :
    IsStronglyEmbedded (Y.comap f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have hmap := Subgroup.map_comap_eq_self_of_surjective hf Y
    rw [htop, Subgroup.map_top, MonoidHom.range_eq_top.mpr hf] at hmap
    exact hY.ne_top hmap.symm
  · obtain ⟨y, hyY, hy⟩ := hY.exists_involution
    obtain ⟨x, hx, hfx⟩ := involution_lift_of_odd_kernel f hodd hy (hf y)
    exact ⟨x, show f x ∈ Y from hfx.symm ▸ hyY, hx⟩
  · intro g hg x hxY hxright hx
    have hfg : f g ∉ Y := hg
    have hfx : IsInvolution (f x) := involution_image_of_odd_kernel f hodd hx
    have hfxright : f x ∈ rightConjugate Y (f g) := by
      obtain ⟨v, hv, hvx⟩ := Subgroup.mem_map.mp hxright
      refine Subgroup.mem_map.mpr ⟨f v, hv, ?_⟩
      change g⁻¹ * v * (g⁻¹)⁻¹ = x at hvx
      change (f g)⁻¹ * f v * ((f g)⁻¹)⁻¹ = f x
      have heq := congrArg f hvx
      simpa only [map_mul, map_inv] using heq
    exact hfg (hY.mem_of_involution_mem_rightConjugate hxY hfxright hfx)

theorem strongly_embedded_preimage_of_odd_kernel (f : G →* K)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (Y : Subgroup K) (hY : fusionStronglyEmbedded Y) :
    fusionStronglyEmbedded (Y.comap f) :=
  order_strong_embedding_of_native
    (strong_embedding_preimage_of_odd_kernel f hf hodd Y
      (native_strong_embedding_of_order_conditions hY))

theorem strongly_embedded_of_odd_kernel_image (f : G →* K)
    (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (A : Subgroup G) (hker : f.ker ≤ A)
    (himage : fusionStronglyEmbedded (A.map f)) :
    fusionStronglyEmbedded A := by
  have h := strongly_embedded_preimage_of_odd_kernel f hf hodd (A.map f) himage
  rwa [Subgroup.comap_map_eq_self hker] at h

end CFSG.ComponentClassification.AschbacherTightEmbedding
