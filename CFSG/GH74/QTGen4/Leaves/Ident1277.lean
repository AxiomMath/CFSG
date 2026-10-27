module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.Vol2.Ch12Sec7Statements

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Quasithin.H13 CFSG.Open CFSG.Blueprint

theorem card_alt6_ident : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_quot_centralizer {G : Type} [Group G] [Finite G] {L V : Subgroup G}
    [((Subgroup.centralizer (V : Set G)).subgroupOf L).Normal]
    (hcen : Nat.card (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)) = 3)
    (e : (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ⧸
        Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) ≃*
      alternatingGroup (Fin 6)) :
    Nat.card (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L) = 1080 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L))
  rw [Nat.card_congr e.toEquiv, card_alt6_ident, hcen] at h1
  omega

theorem false_of_hyp1271_gen4 {G : Type} [Group G] [Finite G] (hG : CFSG.GH74.Gen4 G)
    {T L V : Subgroup G} (hH : Hyp1271 G T L V) : False := by
  obtain ⟨hyp, hA6⟩ := hH
  obtain ⟨hN, -, hcen, ⟨e⟩⟩ := hA6
  have := hN
  have hL1 : 27 ∣ Nat.card ↥L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((Subgroup.centralizer (V : Set G)).subgroupOf L), card_quot_centralizer hcen e]
    exact (by norm_num : (27 : ℕ) ∣ 1080).mul_right _
  obtain ⟨P, rfl⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hInH : CFSG.Quasithin.InH (P : Subgroup G) (L ⊔ P) :=
    ⟨le_sup_right, hyp.faithful.1.2.2.2⟩
  have hO2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ 20160 :=
    CFSG.GH74.QTGen4.modO2_dvd_of_inH hG hyp.qtke.2.1 P hInH le_sup_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥L))
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  rw [hk] at hsplit
  rw [hsplit] at hL1
  have h27 : 27 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 27 2)).dvd_of_dvd_mul_right hL1
  have h20160 := h27.trans hO2
  omega

end CFSG.GH74.QTGen4.Leaves
