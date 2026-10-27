module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
  (conjugationHom_eq_one_iff)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (coordinate_plus_pointFamilyAut_eq_top)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)

variable {H : Type} [Group H] {n p f : ℕ}

theorem oKer_coordinatePlus (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    OKer (coordinateQuadPlus n K) := by
  obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_plus h K hK e
  intro g hg
  exact (conjugationHom_eq_one_iff _ hQ hS (coordinate_model_intrinsic_plus h K hK e).2.1.2.1
    g).1 hg

theorem oSurj_coordinatePlus (h : StatedClassicalModel H .POmegaPlus n p f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ f) (hn : 5 ≤ n)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    OSurj (coordinateQuadPlus n K) := by
  have h1 := coordinate_plus_pointFamilyAut_eq_top (K := K) hn
  have h2 := coordinate_plus_family_eq_matrixImage h K hK e
  intro α
  have hα : α ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [← h2, h1]
    trivial
  obtain ⟨g, hg⟩ := hα
  exact ⟨g, hg.symm⟩

theorem oKer_coordinateMinus (h : StatedClassicalModel H .POmegaMinus n p f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    OKer (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c) := by
  obtain ⟨-, hQ, hS, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  intro g hg
  exact (conjugationHom_eq_one_iff _ hQ hS
    (coordinate_model_intrinsic_minus h K hK b c hirr e).2.1.2.1 g).1 hg

theorem oSurj_coordinateMinus (h : StatedClassicalModel H .POmegaMinus n p f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = p ^ f) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : H ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    OSurj (coordinateQuadMinus n K (by have := h.1.2.2; omega) b c) := by
  have hn1 : 1 ≤ n := by have := h.1.2.2; omega
  have h1 := (orthogonal_geometry_tail_model_point_family_invariant H .POmegaMinus (Or.inr rfl) n
    p f h hn1 K hK b c hirr).2
  have h2 := coordinate_minus_family_eq_matrixImage h hn1 K hK b c hirr e
  intro α
  have hα : α ∈ matrixProjectiveImage (coordinateQuadMinus n K hn1 b c) := by
    rw [← h2, h1]
    trivial
  obtain ⟨g, hg⟩ := hα
  exact ⟨g, hg.symm⟩

end CFSG.ComponentClassification.Burgoyne.O
