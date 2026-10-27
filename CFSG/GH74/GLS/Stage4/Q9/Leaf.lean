module

public import CFSG.GH74.GLS.Stage4.RestCases
public import CFSG.GH74.GLS.Stage4.Q9.Setting

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Rest
  CFSG.Assembly.LowTwoRank

@[expose] def Q9SettingOf : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Std G → pRank 2 G = 3 →
    ∀ (Gs : Type) [Group Gs], IsTwoCentralG2TypeG2At G Gs 9 9 → Ch6Bad3 G →
      ∃ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂),
        Nonempty (Q9Setting G z K₁ K₂ F₁ F₂)

end CFSG.GH74.GLS.Stage4.Q9
