module

public import CFSG.ClassicalInvolution.AschTight.Lemma33
public import CFSG.ClassicalInvolution.Uniform.UStand
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected.AschTight

@[expose] def ZLinkFacts3 : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z] (Ψ : Set (Subgroup Z)) (ι : Type)
    (D : Q3.LieSystemData3 ι Z Ψ), HypOmegaModU (.sl2 3 1) Ψ →
    (∀ M ∈ Ψ, ∀ M' ∈ twinSet Ψ M, M' = M) →
    ∀ (M₁ M₂ : Subgroup Z), M₁ ∈ Ψ → M₂ ∈ omegaNbr Ψ M₁ →
      ∀ (i : ι) (R₁ R₂ : Subgroup (D.kind i).G), R₁ ∈ (D.kind i).fund → R₂ ∈ (D.kind i).fund →
        M₁ = R₁.map (D.hom i) → M₂ = R₂.map (D.hom i) →
          (∀ u v : Z, IsUniqueInvolution M₁ u → IsUniqueInvolution M₂ v →
            (D.hom i).range ≤ Subgroup.centralizer ({u} : Set Z) ⊔
              Subgroup.centralizer ({v} : Set Z) ⊔ Subgroup.centralizer ({u * v} : Set Z)) ∧
          (∀ M ∈ Ψ, ∀ R : Subgroup (D.kind i).G, R ∈ (D.kind i).fund →
            M = R.map (D.hom i) → ∃ g : Z, M = conjSub g M₁)

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
