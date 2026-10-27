module

import CFSG.Milestones.SE_simple_strong_embedding_models
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.StronglyEmbedded.BenderNormalSeries

public section

namespace CFSG.Holt.General

open MulAction

section Bender

theorem fusionIsBenderGroup_of_isStronglyEmbedded {X : Type*} [Group X] [Finite X]
    [IsSimpleGroup X] {H : Subgroup X} (hH : CFSG.IsStronglyEmbedded H) :
    CFSG.Open.fusionIsBenderGroup X := by
  refine CFSG.Open.fusionIsBenderGroup_of_isBenderGroup
    (CFSG.Milestones.bender_suzuki H ⟨hH.1, hH.2.1, fun g hg => ?_⟩)
  simpa only [CFSG.conjugate, inv_inv] using hH.2.2 g⁻¹ fun h => hg (H.inv_mem_iff.mp h)

end Bender

end CFSG.Holt.General
