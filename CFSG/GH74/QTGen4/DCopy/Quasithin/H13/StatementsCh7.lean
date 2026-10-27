module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Matrix

@[expose] def Stmt7_0_1_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L I : Subgroup G), FSU G T L I →
    ∃ _ : IsMulCommutative ↥(fsuV T I), IsElemAbelian 2 (fsuV T I) ∧
      fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      (Concl701FF T L I ∨ Concl701J4 T L I ∨ Concl701Orth T L I ∨ Concl701Four T L I)

end CFSG.Quasithin.H13
