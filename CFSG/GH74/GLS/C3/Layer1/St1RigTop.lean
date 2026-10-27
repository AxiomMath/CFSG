module

public import CFSG.GH74.GLS.C3.Layer1.St1RigMain
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH2

public section

namespace CFSG.GH74.GLS

open TwoThin

theorem b_ig_6_10_h2_proved : B_ig_6_10_h2 := by
  intro G _ _ hG h3 x K hILo _
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(Subgroup.centralizer ({y} : Set G)) :=
    fun y hy => rankThreeCentralizers G hG.1 hG.2.1 h3 y hy
  exact C3.Layer1.PumpRigid.exists_twoTerminal hR hILo

theorem b_ig_6_10_proved : B_ig_6_10 := b_ig_6_10_of_h2 b_ig_6_10_h2_proved

end CFSG.GH74.GLS
