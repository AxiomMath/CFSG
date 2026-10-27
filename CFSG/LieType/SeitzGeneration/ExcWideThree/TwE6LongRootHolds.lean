module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootQ1
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootGen
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootNormalizerLevi
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrrGlue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

section Holds


theorem twE6LongRootParabolicStructure_holds : TwE6LongRootParabolicStructure :=
  TwE6LongRoot.q1_holds

theorem twE6LongRootIrreducible_holds : TwE6LongRootIrreducible := by
  intro K _ _ σ q hr hσ hK X Xm hpair M hXM hMQ hnorm
  exact irreducible_of_standard σ
    (fun M hXM hMQ hnorm => irreducible_std σ q hr hσ hK M hXM hMQ hnorm) X Xm hpair M hXM hMQ hnorm

theorem twE6LongRootGenerates_holds : TwE6LongRootGenerates := by
  intro K _ _ σ q _ _ _ X Xm hpair
  have hQ : (twE6LongRootRadical (twE6RootSubgroup K σ e6HighestRoot)).map
      (twistedE6RootGroup K σ).subtype =
        graphFixedParabolicRadical TwistTag.E6 K σ.toRingHom TwE6LongRoot.J0 := by
    rw [radical_std_eq σ]
    exact Subgroup.map_subgroupOf_eq_of_le
      (graphFixedParabolicRadical_le_graphFixedRootGroup TwistTag.E6 K σ.toRingHom TwE6LongRoot.J0)
  exact generates_of_standard σ
    (Gen.twE6LongRootGenerates_of_structure σ (twE6LongRootParabolic_map_subtype σ)
      (twE6LongRootParabolic_maximal σ) hQ (graphFixedParabolicLevi_subgroupOf_le_normalizer σ))
    X Xm hpair

end Holds

end CFSG.LieType.SeitzGeneration.ExcWideThree
