module

public import CFSG.CGT.Timmesfeld75.JLemmaRoot
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75

@[expose] def Lemma26Nondeg {K : Type} [Group K] (T : Subgroup K) : Prop :=
  ∃ d ∈ classD T, ∃ e ∈ classD T, orderOf (d * e) = 4

@[expose] def Lemma26ExclAt (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] [IsSimpleGroup K] (T : Subgroup K), Lemma26Hyp K T →
    Lemma26Nondeg T → ¬ P K

end CFSG.CGT.T75E
