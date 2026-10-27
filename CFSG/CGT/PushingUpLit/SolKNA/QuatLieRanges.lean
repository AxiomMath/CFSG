module

public import CFSG.CGT.PushingUpLit.SolKNA.Quaternion
public import CFSG.ClassicalInvolution.SmallCases.Partition

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)

@[expose] def QLSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), STSetting G K →
    ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
      CFSG.Blueprint.OddLieType G → CFSG.ClassicalInvolution.TwoSubgroupsFourGenerated G →
        MTOutcome G K R

@[expose] def QLLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), STSetting G K →
    ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
      CFSG.Blueprint.OddLieType G → ¬ CFSG.ClassicalInvolution.TwoSubgroupsFourGenerated G →
        MTOutcome G K R

theorem quaternionInspectionLie_of_ranges (hS : QLSmall) (hL : QLLarge) :
    QuaternionInspectionLie := by
  intro G _ _ hKP hs hna K hK hM hF R hq hodd
  have hst : STSetting G K := ⟨hs, hna, hK, hM, hF⟩
  by_cases hg : CFSG.ClassicalInvolution.TwoSubgroupsFourGenerated G
  · exact hS G K hst R hq hodd hg
  · exact hL G K hst R hq hodd hg

end CFSG.CGT.PushingUpLit.SolKNA
