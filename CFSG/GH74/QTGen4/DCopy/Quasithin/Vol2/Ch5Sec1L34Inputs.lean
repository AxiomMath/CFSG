module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def DSSzStatement_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    (∃ a : ℕ, 1 ≤ a ∧ Nonempty (oTwoQuot ↥L1 ≃* CFSG.Open.Sz a)) → ¬ Group.IsSolvable ↥L2 →
      S ≤ L1 ∧ S ≤ L2

end CFSG.Quasithin.H13
