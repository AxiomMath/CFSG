module

public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

@[expose] def E3S3GenL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel (FStarQuot X) .PSL 3 p f →
      ∀ t s : X, orderOf t = 2 → orderOf s = 2 → t ∈ genFittingFStar X →
        s ∈ genFittingFStar X → t * s = s * t → s ≠ t →
          Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤

@[expose] def E3S3GenU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSimpleGroup ↥(genFittingFStar X) →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel (FStarQuot X) .PSU 3 p f →
      ∀ t s : X, orderOf t = 2 → orderOf s = 2 → t ∈ genFittingFStar X →
        s ∈ genFittingFStar X → t * s = s * t → s ≠ t →
          Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤

@[expose] def E3S3GenM12 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.Carrier .M12) →
    ∀ t s : X, orderOf t = 2 → t * s = s * t → s ≠ t → (∃ g : X, s = g * t * g⁻¹) →
      Subgroup.centralizer ({t} : Set X) ⊔ Subgroup.centralizer ({s} : Set X) = ⊤

end CFSG.ClassicalInvolution.Q3.TL4
