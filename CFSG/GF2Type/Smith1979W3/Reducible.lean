module

public import CFSG.GF2Type.Smith1979W3.Dispatch
public import CFSG.LargeExtraspecial.DW3Data
public import CFSG.LargeExtraspecial.DWTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification

@[expose] def DWSplitWidthThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → NotWeaklyClosed S → S.IsReducible →
      ∃ (W₁ W₂ : Submodule (ZMod 2) S.Qt) (H : DW.W3.Hyp S W₁ W₂),
        Function.Surjective H.res ∧
          ∃ x : G, x ∈ S.M ∧ x ∉ S.QG ∧ x * x = 1 ∧
            ∃ A : Subgroup G, IsElementaryAbelian 2 A ∧ DW.MaxEA S A ∧ ∀ a ∈ A, x * a = a * x

end CFSG.GF2Type.Smith1979W3
