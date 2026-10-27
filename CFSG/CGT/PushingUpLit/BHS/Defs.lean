module

public import CFSG.RankThree.PartOne.S9.Defs
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.RankThree.PartOne

variable {G : Type*} [Group G]

@[expose] def IsMinParabolic2 (T P : Subgroup G) : Prop :=
  IsSylowOf 2 T P ∧ ¬ P ≤ Subgroup.normalizer (T : Set G) ∧
    ∃ M : Subgroup G, T ≤ M ∧ M < P ∧ ∀ X : Subgroup G, T ≤ X → X < P → X ≤ M

end CFSG.CGT.PushingUpLit.BHS
