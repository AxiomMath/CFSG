module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Second

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

structure Lemma36DataQ (s : TauCeti.SporadicName) (Q : PairClass) (m n : ℕ) : Prop where
  bound : 2 * 2 ^ m < n
  data : ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), OddCover s L →
    Q H L K u →
      orderOf u = 2 ∧ u ∈ K ∧ K ≤ L ⊓ centralizer ({u} : Set H) ∧
        (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Characteristic ∧
        CFSG.IsQuasisimple ↥K ∧ Group.IsSolvable ↥(autCentralizer L K) ∧
        twoAdic (autCentralizer L K) ≤ m ∧ InvolutionFixesElem ↥K n

end CFSG.EvenSporadicStandard.Induction
