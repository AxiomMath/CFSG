module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.StatementsCh7

public section
namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise

@[expose] def TmpL6_3_2_2_six_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L I : Subgroup G), FSU G T L I →
    fsuCVM T L I ≠ ⊥ → IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) →
      fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆ ∧
        ∃ _ : IsMulCommutative ↥(fsuV T I),
          IsFFModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L ⊔ T) (fsuV T I))

end CFSG.Quasithin.Vol2.Ch11
