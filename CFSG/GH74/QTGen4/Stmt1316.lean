module

public import CFSG.GH74.QTGen4.Statements
public import CFSG.GH74.QTGen4.OrderOverH
import CFSG.Adapters.LieModelSmallOrders

public section

namespace CFSG.GH74.QTGen4

open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open CFSG.Blueprint

theorem card_lieModel_psu_three_three {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Blueprint.LieModel.card_psu_three_three h

theorem not_lieModel_psu_three_three_of_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T L : Subgroup G} (hH : QTH13 G T L) : ¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 := by
  intro hU
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hH.sylow
  have hInH : CFSG.Quasithin.InH (P : Subgroup G) (L ⊔ P) :=
    ⟨le_sup_right, hH.faithful.1.2.2.2⟩
  have hd := modO2_dvd_of_inH hG hH.qtke.2.1 P hInH (le_sup_left : L ≤ L ⊔ P)
  rw [card_lieModel_psu_three_three hU] at hd
  omega

theorem stmt13_3_16_GH : Stmt13_3_16_GH :=
  fun _ _ _ hc _ _ hH => not_lieModel_psu_three_three_of_gen4 hc.1 hH

end CFSG.GH74.QTGen4
