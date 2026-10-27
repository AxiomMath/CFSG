module

public import CFSG.ClassicalInvolution.Q3.TL4OddCover

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Open


@[expose] def E4CoverOddFree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (CoverSp4 X ∨ CoverSL4 X) →
    ∀ v : X, orderOf v = 2 →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({v} : Set X)) = ⊥

end CFSG.ClassicalInvolution.Q3.TL4
