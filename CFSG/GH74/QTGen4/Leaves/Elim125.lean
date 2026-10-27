module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec5Statements
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13 CFSG.Open

theorem card_modO2_dvd_of_hyp1223 {G : Type} [Group G] [Finite G] (hG : CFSG.GH74.Gen4 G)
    {T L V : Subgroup G} (hyp : Hyp1223 G T L V) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ 20160 := by
  obtain ⟨P, rfl⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hInH : CFSG.Quasithin.InH (P : Subgroup G) (L ⊔ P) :=
    ⟨le_sup_right, hyp.faithful.1.2.2.2⟩
  exact CFSG.GH74.QTGen4.modO2_dvd_of_inH hG hyp.qtke.2.1 P hInH le_sup_left

theorem stmt12_5_1_F4_holds : Stmt12_5_1_F4 := by
  intro G _ _ T L V hH hq
  obtain ⟨e⟩ := hq
  have h := card_modO2_dvd_of_hyp1223 Finite4.gen4 hH
  rw [Nat.card_congr e.toEquiv, card_sl_five_zmod_two] at h
  exfalso
  omega

end CFSG.GH74.QTGen4.Leaves
