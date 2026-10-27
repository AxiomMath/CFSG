module

public import CFSG.ClassicalInvolution.RouteD.TWEB4Class

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B3

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.ClassicalInvolution.RouteD.TWE.B4
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Det

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem class_b3_model_det (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} [Fact p.Prime] [CharP K p] (hd : Module.finrank K V = 7) {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1)
    (hdet : LinearEquiv.det g = 1) (FJ FN : OFrame Q) (hgJ : ∀ x ∈ FJ.span, g x = x)
    (hgN : ∀ x ∈ FN.span, g x ∈ FN.span) {A : SL(2, K)} (hA1 : A ≠ 1) (hAp : A ^ p = 1)
    (hinv : ∀ v, g (FN.La A v) = (FN.La A).symm (g v)) :
    ∃ π ρ : HypPair Q, π.Orth ρ ∧ hypPlane π ⊔ hypPlane ρ = FN.span ∧
      negSpace g = hypPlane π ∧ (∀ y ∈ π.perp, g y = y) := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨π, ρ, horth, hsup, hπ, hρ⟩ := eigen_planes_of_inverted hodd hQ hgO hg2 FN hgN hA1 hAp
    hinv
  have hπle : hypPlane π ≤ negSpace g := fun x hx => mem_negSpace_iff'.mpr (hπ x hx)
  have hJle : FJ.span ≤ posSpace g := fun x hx => mem_posSpace_iff'.mpr (hgJ x hx)
  have hsum : Module.finrank K (posSpace g) + Module.finrank K (negSpace g) = 7 := by
    rw [← hd]
    exact Submodule.finrank_add_eq_of_isCompl (isCompl_pos_neg h2 hg2)
  have hpos4 : 4 ≤ Module.finrank K (posSpace g) := by
    have := Submodule.finrank_mono hJle
    rwa [FJ.finrank_span] at this
  have hneg2 : 2 ≤ Module.finrank K (negSpace g) := by
    have := Submodule.finrank_mono hπle
    rwa [finrank_hypPlane] at this
  have heven : Even (Module.finrank K (negSpace g)) :=
    CFSG.ClassicalInvolution.ModelFacts.even_finrank_minusSp h2 hg2 hdet
  have hneg : negSpace g = hypPlane π := by
    have h2' : Module.finrank K (negSpace g) = 2 := by
      obtain ⟨k, hk⟩ := heven
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane, h2'])).symm
  exact ⟨π, ρ, horth, hsup, hneg, fun y hy => eq_self_of_perp_plane h2 hgO hg2 π hneg hy⟩

end Det

end CFSG.ClassicalInvolution.RouteD.TWE.B3
