module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321Steps

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def Step3_3_21fQ_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
    Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
    ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L → InducesInnerOn T L →
      ⁅pCoreOf 2 L, L⁆ ≤ vPlus L T → pCoreOf 2 (L ⊔ T) = vPlus L T

end CFSG.Quasithin.H13
