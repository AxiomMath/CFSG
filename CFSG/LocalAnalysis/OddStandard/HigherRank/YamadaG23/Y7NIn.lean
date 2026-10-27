module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Ext26

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def Aut29Idx : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec2.IsExt26 1 X →
    ¬ SplitsOver (⊤ : Subgroup X) (pCoreOf 2 (⊤ : Subgroup X)) → (innerAut X).index ≤ 2

end CFSG.OddStandard.HigherRank.YamadaG23
