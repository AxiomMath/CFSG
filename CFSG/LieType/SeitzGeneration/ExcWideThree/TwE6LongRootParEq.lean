module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootNormalizerRadical
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootRadical

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section ParEq

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem radical_std_eq :
    twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot) =
      (graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom J0).subgroupOf
        (twistedE6RootGroup K σ) := by
  refine le_antisymm ?_ (graphFixedParabolicRadical_subgroupOf_le_twE6LongRootRadical σ)
  intro g hg
  have h1 := Subgroup.mem_map_of_mem (twistedE6RootGroup K σ).subtype hg
  rw [twE6LongRootRadical_map_subtype σ] at h1
  exact pCore_graphFixedParabolic_le K σ h1

end ParEq

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot
