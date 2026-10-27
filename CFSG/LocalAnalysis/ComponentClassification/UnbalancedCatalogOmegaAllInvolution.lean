module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaLinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFieldInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaFullCentralizerCore

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

namespace OmegaRadical

variable {K : Type} [Field K] {d : ℕ}

theorem semilinearInvolutionOddCore_of_cases {Q : QuadraticForm K (Fin d → K)}
    (hlin : LinearInvolutionOddCore Q) (hfield : FieldInvolutionOddCore Q) :
    SemilinearInvolutionOddCore Q := by
  intro H hInn hHE α hαH hα2
  obtain ⟨g, rfl⟩ := hHE hαH
  by_cases hg : g.val.right = 1
  · exact hlin H hInn hHE g hg hαH hα2
  · exact hfield H hInn hHE g hg hαH hα2

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_all_involution_semilinear_odd_core (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    match t with
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)),
          SemilinearInvolutionOddCore (coordinateQuadPlus n K) ∧
            (5 ≤ n → FullInvolutionOddCore (coordinateQuadPlus n K))
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        ∀ _e : G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)),
          SemilinearInvolutionOddCore (coordinateQuadMinus n K hn b c) ∧
            FullInvolutionOddCore (coordinateQuadMinus n K hn b c)
    | _ => False := by
  have hlin := even_orthogonal_linear_involution_semilinear_odd_core G t ht n f h
  have hfield := even_orthogonal_field_involution_semilinear_odd_core G t ht n f h
  rcases ht with rfl | rfl
  · intro K _ _ hK e
    obtain ⟨hF, htop⟩ := hfield K hK e
    have hsemi := semilinearInvolutionOddCore_of_cases (hlin K hK e) hF
    exact ⟨hsemi, fun h5 => fullInvolutionOddCore_of_image_eq_top (htop h5) hsemi⟩
  · intro hn K _ _ hK b c hirr e
    obtain ⟨hF, htop⟩ := hfield hn K hK b c hirr e
    have hsemi := semilinearInvolutionOddCore_of_cases (hlin hn K hK b c hirr e) hF
    exact ⟨hsemi, fullInvolutionOddCore_of_image_eq_top htop hsemi⟩

end CFSG.ComponentClassification.UnbalancedCatalog
