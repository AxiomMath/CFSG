module

public import CFSG.Quasithin.H13.U3Hull
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3HullFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4

variable
  {T L V : Subgroup G}
  [IsElementaryAbelian 2 V] {z : G} (S : HullSetting_F4 G T L V z)
include S

theorem fsuV1_eq_V₁_F4 :
    fsuV1 T V = S.V₁_F4 := by
  rw [fsuV1_eq S.hF, S.hVz_F4, S.V₁_eq_F4]

theorem g1_eq_H_F4 :
    A6.g1 T V = S.H_F4 := by
  show normalizer (fsuV1 T V : Set G) = S.H_F4
  rw [S.fsuV1_eq_V₁_F4, S.normalizer_V₁_F4]

theorem isV2_F4 : A6.IsV2 T V S.V₂_F4 :=
  ⟨by rw [S.fsuV1_eq_V₁_F4]; exact S.le12_F4, S.le23_F4.trans S.le3_F4, S.T_normalizes_V₂_F4, S.card_V₂_F4⟩

end HullSetting_F4

end CFSG.Quasithin.H13.U3
