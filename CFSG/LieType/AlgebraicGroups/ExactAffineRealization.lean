module

public import CFSG.LieType.AlgebraicGroups.ExactAffineRealizationGroups
public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley WithConv TensorProduct

open scoped CFSG.ConvolutionPoints

theorem exceptional_Lang_exact_affine_group_realization
    (k : Type) [Field k] [IsAlgClosed k]
    (τ : Tag) :
    (IsPointClosed k (groupPoints τ k) ∧
      IsConnectedAlgebraicSubgroup k (adjointPointSubgroup τ k) ∧
      Algebra.Smooth k (GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k)) ∧
      IrreducibleSpace
        (PrimeSpectrum (GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k))) ∧
      ∃ e : WithConv ((GLCoord k (Label τ) ⧸ subgroupIdeal (adjointPointSubgroup τ k)) →ₐ[k] k) ≃*
          adjointGroup τ k, ∀ φ,
        ((e φ : adjointGroup τ k) : ModGL τ k) =
          (modGLPoint τ k).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _)))) ∧
    ∀ (M : ℕ) (ψ : adjointGroup τ k →* Matrix.GeneralLinearGroup (Fin M) k),
      (∀ i, ∃ φ : GLCoord k (Fin M) →ₐ[k] Polynomial k,
        ∀ c, toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (ψ (adjX τ k i c))) →
      (∀ i, ∃ φ : GLCoord k (Fin M) →ₐ[k] Polynomial k,
        ∀ c, toConv ((Polynomial.aeval c).comp φ) = glPointEquiv (ψ (adjY τ k i c))) →
      IsPointClosed k (graphPoints τ k ψ) ∧
        IsConnectedAlgebraicSubgroup k (graphPointSubgroup ψ) ∧
        Algebra.Smooth k
          (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ)) ∧
        IrreducibleSpace (PrimeSpectrum
          (GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸ subgroupIdeal (graphPointSubgroup ψ))) ∧
        ∃ e : WithConv ((GLCoord k (Label τ) ⊗[k] GLCoord k (Fin M) ⧸
            subgroupIdeal (graphPointSubgroup ψ)) →ₐ[k] k) ≃* graphSubgroup ψ, ∀ φ,
          ((e φ : graphSubgroup ψ) : ModGL τ k × Matrix.GeneralLinearGroup (Fin M) k) =
            (modGLPairPoint τ k M).symm (toConv (φ.ofConv.comp (Ideal.Quotient.mkₐ k _))) := by
  obtain ⟨-, -, -, hgraph, hcons, hirr⟩ := exceptional_Lang_rootword_Bruhat_regular_cover τ k
  refine ⟨adjointGroup_realization hcons hirr, fun M ψ hx hy => ?_⟩
  obtain ⟨-, -, -, hgcons, hgirr⟩ := hgraph M ψ hx hy
  exact graphSubgroup_realization ψ hgcons hgirr

end CFSG.LieType.AlgebraicGroups
