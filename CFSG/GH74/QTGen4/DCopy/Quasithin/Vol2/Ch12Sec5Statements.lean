module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Stmt12_5_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      ∃ _ : IsMulCommutative ↥V, BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 5 1

end CFSG.Quasithin.H13
