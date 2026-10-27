module

public import CFSG.LieType.AlgebraicGroups.TangentSpace
public import Mathlib.RingTheory.Smooth.Basic
public import CFSG.LieType.AlgebraicGroups.InnerTwistDifferential
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupIdeal
public import CFSG.LieType.AlgebraicGroups.ThreeFixedQuotient
public import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupClosed
import CFSG.LieType.AlgebraicGroups.ToralCentralizerComponent
import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramComorphism
import TauCeti.RingTheory.Smooth.GeometricallyReduced
public import CFSG.Open.Defs

open scoped CFSG.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open WithConv

variable {k : Type} [Field k] [IsAlgClosed k] {A : Type} [CommRing A] [HopfAlgebra k A]
  [Algebra.FiniteType k A]

@[expose] def adFixedTangent (M : Subgroup (WithConv (A →ₐ[k] k)))
    (S : Set (WithConv (A →ₐ[k] k))) :
    Submodule k (TangentSpace k (A ⧸ subgroupIdeal M) (Bialgebra.counitAlgHom k _)) where
  carrier := {D | ∀ g ∈ S, ∀ a : A,
    D.1 (Ideal.Quotient.mk _ (innerCo g a)) = D.1 (Ideal.Quotient.mk _ a)}
  add_mem' {D E} hD hE g hg a := by
    change D.1 _ + E.1 _ = D.1 _ + E.1 _
    rw [hD g hg a, hE g hg a]
  zero_mem' _ _ _ := rfl
  smul_mem' c D hD g hg a := by
    change c • D.1 _ = c • D.1 _
    rw [hD g hg a]

end CFSG.LieType.AlgebraicGroups

end
