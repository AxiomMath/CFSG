module

public import CFSG.ClassicalInvolution.Q3.TL4OddCover

public section

namespace CFSG.ClassicalInvolution.Q3.TL4


@[expose] def E4CoverGen : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (CoverSp4 X ∨ CoverSL4 X) →
    ∀ u w : X, u * u = 1 → w * w ∈ Subgroup.center X → w * w ≠ 1 → u * w = w * u →
      Subgroup.centralizer ({u} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
        Subgroup.centralizer ({u * w} : Set X) = ⊤

end CFSG.ClassicalInvolution.Q3.TL4
