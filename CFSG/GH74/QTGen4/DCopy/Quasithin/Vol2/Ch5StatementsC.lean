module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Statements

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def Ch5L2ChoiceExists_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L H B D : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D →
      ∃ L₂ : Subgroup G, IsL2Choice T H L₂

end CFSG.Quasithin.H13
