module

public import CFSG.CGT.PushingUpLit.NineChoice
public import CFSG.CGT.PushingUpLit.Statements

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.Assembly

@[expose] def AschbacherNineContent : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    ∀ (T : Sylow 2 G) (I H S : Subgroup G),
      NineChoice (characteristicCoreStar (T : Subgroup G)) I H S → ∃ X : Subgroup G, InClassXG X

theorem factorizationTwo_of_nineContent (h : AschbacherNineContent) :
    AschbacherFactorizationTwo := fun G _ _ hK hchar T hM => by
  by_cases hse : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder
      (characteristicCoreStar (T : Subgroup G))
  · exact Or.inl hse
  · obtain ⟨I, H, S, hc⟩ := exists_nineChoice hchar T hM hse
    exact Or.inr (h G hK hchar T I H S hc)

end CFSG.CGT.PushingUpLit
