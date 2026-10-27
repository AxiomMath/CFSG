module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def DSCStatement_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (L1 L2 S : Subgroup G), Hyp111 L1 L2 S →
    IsQuasithinSub (L1 ⊔ L2 ⊔ S) →
    ((S.subgroupOf (S ⊔ borelOf L1 S)).Normal ∨ (S.subgroupOf (S ⊔ borelOf L2 S)).Normal) →
    ¬ Group.IsSolvable ↥L1 →
    ¬ (Nonempty (oTwoQuot ↥L2 ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥L2 ≃* ↥(Sz 0)))

end CFSG.Quasithin.H13
