module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsCh7

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

@[expose] def Stmt7_1_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L I : Subgroup G), Hyp7_0_2 G T L I →
    ∃ _ : IsMulCommutative ↥(fsuV T I), Rows7_1_1 T L I

end CFSG.Quasithin.H13
