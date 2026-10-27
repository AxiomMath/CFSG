module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.Skeleton

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def StageTheorem1513_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M →
    (Nat.card (VZ T M) = 4 ∧ SixModels G) ∨ IsOFourPlusAction M (VZ T M)

@[expose] def StageTheorem1531_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → ¬ IsOFourPlusAction M (VZ T M)

@[expose] def StageTheorem14625_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Hyp1421 G T M → SixModels G

@[expose] def StageRankNotTwo_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → Nat.card (VZ T M) ≠ 4 → IsOFourPlusAction M (VZ T M)

theorem stageTheorem1513_of_parts_F4 (h14625 : StageTheorem14625_F4) (hR2 : StageRankTwoHyp1421)
    (hR : StageRankNotTwo_F4) : StageTheorem1513_F4 := by
  intro G _ _ T Mc M h hM
  by_cases h4 : Nat.card (VZ T M) = 4
  · exact Or.inl ⟨h4, h14625 G T M (hR2 G T Mc M h hM h4)⟩
  · exact Or.inr (hR G T Mc M h hM h4)

end CFSG.Quasithin
