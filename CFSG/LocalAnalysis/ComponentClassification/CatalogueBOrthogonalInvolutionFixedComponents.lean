module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionFixedComponents

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CatalogueBOrthogonalSemilinear CatalogueBOrthogonalPointData
open CatalogueBOrthogonalInvolutionRepresentation CatalogueBOrthogonalFixedTransfer

variable {K : Type} [Field K] [Finite K] {d : ℕ}

@[expose] def conjFixedEquiv {P : Type*} [Group P] (alpha beta : MulAut P) :
    FixedCommutingProduct.fixedSubgroup alpha ≃*
      FixedCommutingProduct.fixedSubgroup (beta⁻¹ * alpha * beta) :=
  fixedEquivOfIntertwining beta.symm alpha (beta⁻¹ * alpha * beta) fun x => by
    change beta.symm (alpha x) = beta.symm (alpha (beta (beta.symm x)))
    rw [MulEquiv.apply_symm_apply]

theorem fixed_pComponent_quasisimple_of_representation (ℓ f : ℕ) (hℓ : ℓ.Prime)
    (hodd : ℓ ≠ 2) (hf : 1 ≤ f) (hcard : Nat.card K = ℓ ^ f) (hd : 2 ≤ d)
    (Q : QuadraticForm K (Fin d → K)) (hQ : Q.polarBilin.Nondegenerate)
    (hrep : SemilinearRepresentation Q) (alpha : MulAut (matrixProjectiveDerived Q))
    (h2 : alpha * alpha = 1) (h1 : alpha ≠ 1) :
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  obtain ⟨beta, g, hg, hsigma, ⟨c, hc⟩, hns, -⟩ := hrep.2 alpha h2 h1
  have key := fixed_pComponent_quasisimple_of_matrix ℓ f hℓ hodd hf hcard hd Q hQ g hsigma c hc
    hns
  intro p hp L hL
  have e : FixedCommutingProduct.fixedSubgroup alpha ≃*
      FixedCommutingProduct.fixedSubgroup (matrixProjectiveConjugation Q g) :=
    (conjFixedEquiv alpha beta).trans (MulEquiv.subgroupCongr (congrArg _ hg))
  exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv p e (key p hp) L hL

@[expose] def ModelInvolutionFixedComponents (G : Type) [Group G] (t : StatedLieTag)
    (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
      ∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)), alpha * alpha = 1 →
        alpha ≠ 1 → ∀ r : ℕ, r.Prime →
          ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
            CFSG.IsPComponent r L → CFSG.IsQuasisimple L
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
      ∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)), alpha * alpha = 1 →
        alpha ≠ 1 → ∀ r : ℕ, r.Prime →
          ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
            CFSG.IsPComponent r L → CFSG.IsQuasisimple L
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
      ∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)),
        alpha * alpha = 1 → alpha ≠ 1 → ∀ r : ℕ, r.Prime →
          ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup alpha),
            CFSG.IsPComponent r L → CFSG.IsQuasisimple L
  | _ => False

theorem odd_orthogonal_involution_fixed_p_components {G : Type} [Group G] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ} (hodd : p ≠ 2)
    (h : StatedClassicalModel G t n p f) : ModelInvolutionFixedComponents G t n p f := by
  have hrep := odd_orthogonal_involution_semilinear_representation t ht h
  rcases ht with rfl | rfl | rfl
  · intro K _ _ hK e alpha h2 h1
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_odd h K hK e
    have hn : 3 ≤ n := h.1.2.2.1
    exact fixed_pComponent_quasisimple_of_representation p f h.1.1 hodd h.1.2.1 hK
      (by omega) _ hQ (hrep K hK e) alpha h2 h1
  · intro K _ _ hK e alpha h2 h1
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_plus h K hK e
    have hn : 4 ≤ n := h.1.2.2
    exact fixed_pComponent_quasisimple_of_representation p f h.1.1 hodd h.1.2.1 hK
      (by omega) _ hQ (hrep K hK e) alpha h2 h1
  · intro hn K _ _ hK b c hirr e alpha h2 h1
    obtain ⟨-, hQ, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    have hn4 : 4 ≤ n := h.1.2.2
    exact fixed_pComponent_quasisimple_of_representation p f h.1.1 hodd h.1.2.1 hK
      (by omega) _ hQ (hrep hn K hK b c hirr e) alpha h2 h1

end CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionFixedComponents
