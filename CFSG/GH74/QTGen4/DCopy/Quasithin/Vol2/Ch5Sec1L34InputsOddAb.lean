module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_17_noBlock_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n → ¬ ⁅pCoreOf 2 L, L⁆ ≤ V

end CFSG.Quasithin.H13
