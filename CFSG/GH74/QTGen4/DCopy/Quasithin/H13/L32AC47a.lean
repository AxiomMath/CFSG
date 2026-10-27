module

public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Ambient

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H : Subgroup G}

theorem card_center_cStar_dvd_three_F4 (h28 : Lemma14_7_28_F4) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hK : K ∈ cComp H) : Nat.card (Subgroup.center (cStar K)) ∣ 3 := by
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set Kb := modO2Image H K with hKb
  have hcard : Nat.card (Subgroup.center (cStar K)) = Nat.card (Subgroup.center ↥Kb) :=
    card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)
  set Z := Subgroup.center ↥Kb with hZ
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : ((Z.map Kb.subtype).subgroupOf Kb).Normal := by
    rw [map_subtype_subgroupOf']
    infer_instance
  have hZs : (Z.map Kb.subtype).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le Z) hKbs hZn
  have hZc : Nat.card (Z.map Kb.subtype) = Nat.card Z :=
    Subgroup.card_map_of_injective Kb.subtype_injective
  have hodd : Odd (Nat.card (Z.map Kb.subtype)) := by
    rw [hZc, ← hcard]
    exact odd_card_center_cStar K
  have hle := le_oddCore_of_isSubnormal hZs hodd
  rw [hcard, ← hZc]
  rcases h28 G T L V H S with h0 | h1
  · rw [h0, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot]
    exact one_dvd 3
  · rw [h1] at hle
    have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
    have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := h1 ▸ odd_card_oddCore
    exact (Subgroup.card_dvd_of_le hle).trans (card_modO2Image_dvd_three hL1H hL3 hoddL)

end Ambient

end CFSG.Quasithin.H13.L32A.C
