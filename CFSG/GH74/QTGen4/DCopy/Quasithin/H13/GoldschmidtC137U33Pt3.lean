module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Pt3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace U33Cfg

variable [CFSG.GH74.QTGen4.Finite4 G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
  (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
include h E hF

section Point

variable {A : Subgroup (MulAut (IntMod V h.hVe))}
  (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
  {c : MulAut (IntMod V h.hVe)} (hc : c ∈ autI h.hVe L)
  (hLc : autI h.hVe L ≤ A ⊔ B1.conjAut c A)
  (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4)
  (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
    (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
include hA hc hLc hC132 hn1

theorem blockPart_of_point_F4 : BlockPart L := by
  have hC : ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B := h.no_strong E hA
  have hDE := h.hDE_u33 E hA hc hLc hF.rk_L
  obtain ⟨hCV, -⟩ := b2_19_rel h.hVe h.hred.1 h.hXN h.toBaum.hLeq.symm
    (pCoreOf_isPGroup 2 P) h.hRX h.hVR h.toBaum.hA1 h.toBaum.hA2 h.toBaum.hA3 h.toBaum.hB hC hDE
  obtain ⟨hMS, hLcomp, hset⟩ := h.isMSPair_u33 E hF hA hn1 hCV
  have h132 := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  have hG2 := isG2Block_of_c132 (card_of_psu33 h.hlie) h132
  obtain ⟨hnat, hcomm⟩ := h.natural_of_entry E hF
  exact blockPart_of_psu33 h.hlie (h.isG2Block_h13 hG2 hnat hcomm)

end Point

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
