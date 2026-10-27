module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5A8
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
open CFSG.EvenSporadicStandard.HSStd

@[expose] def ThreeCentralizer7U43 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (N : Subgroup Γ), N.Normal → centralizer (N : Set Γ) = ⊥ →
    LieModel ↥N .PSU 4 3 1 →
    ∀ y : Γ, orderOf y = 3 → ¬ 7 ∣ Nat.card ↥(centralizer ({y} : Set Γ))

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
