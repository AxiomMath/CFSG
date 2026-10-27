module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.H13.L32ASetting

public section

namespace CFSG.GH74.QTGen4

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem false_of_setting147_three {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T L V H : Subgroup G} (S : Setting147 G T L V H)
    (three : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) : False := by
  have hF := S.hyp.fsu
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hF.sylow
  have hIn : InH (P : Subgroup G) H :=
    ⟨le_sup_right.trans S.hz.1.1, S.hz.1.2⟩
  have hd := modO2_dvd_of_inH hG hF.qtke.2.1 P hIn (K := H) le_rfl
  have h27 : Nat.card ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))) = 27 := by
    have := three.2.1
    simpa using this
  have h1 := Subgroup.card_subgroup_dvd_card
    (oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))
  rw [h27] at h1
  have h2 := h1.trans hd
  norm_num at h2

end CFSG.GH74.QTGen4
