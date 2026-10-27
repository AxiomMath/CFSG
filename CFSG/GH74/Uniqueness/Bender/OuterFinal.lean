module

public import CFSG.GH74.Uniqueness.Bender.Outer
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvolutionInner

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

theorem bender_outer_involution
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (α : MulAut K) (hα : α * α = 1)
    (hout : ¬ ∃ g : K, ∀ x : K, α x = g * x * g⁻¹) :
    (∃ y : K, y ≠ 1 ∧ y * y = 1 ∧ α y = y) ∧
      ∀ S : Sylow 2 K, ∃ x : K, α x = x ∧ x ∉ normalizer ((S : Subgroup K) : Set K) := by
  obtain ⟨n, i, e, hT⟩ := isBenderGroup_iff_exists_benderType.mp hK
  refine ⟨hT.exists_fixed_involution α hα, fun S => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy⟩ := CFSG.ComponentClassification.AschbacherToolkit.bender_involution_automorphism_inner
    K (CFSG.Open.fusionIsBenderGroup_of_isBenderGroup hK) α hα ⟨S, hcon⟩
  exact hout ⟨y, fun x => by rw [hy, MulAut.conj_apply]⟩

end CFSG.GH74.Uniqueness.Bender
