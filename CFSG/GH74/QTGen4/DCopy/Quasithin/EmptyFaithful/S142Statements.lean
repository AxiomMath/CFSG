module

public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.Skeleton

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def StageSection146_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    IsMulCommutative ↥(uOfL22 T M) → False

theorem stageTheorem14625_of_parts_F4 (h316 : StageTheorem14316) (h146 : StageSection146_F4) :
    StageTheorem14625_F4 := by
  intro G _ _ T M h
  by_contra hn
  exact h146 G T M h hn (h316 G T M h hn)

end CFSG.Quasithin
