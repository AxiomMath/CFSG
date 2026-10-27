module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.H13.GoldschmidtC137H6Blk
public import CFSG.Quasithin.H13.GoldschmidtC137H6Pt1
public import CFSG.Quasithin.H13.GoldschmidtC137H6Pt2

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [CFSG.GH74.QTGen4.Finite4 G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem point_b_concl_F4 (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4)
    (hCN : ¬ CharNormal (baum (pCoreOf 2 P)) X) (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G))
    (hJ1 : autI h.hVe (thompsonJ (pCoreOf 2 P)) = R1.map F.ρ) : BlockPart L := by
  have hJR : autI h.hVe (thompsonJ (pCoreOf 2 P)) = autI h.hVe (pCoreOf 2 P) := hJ1.trans hR.symm
  have hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)) := by
    rw [← hJR]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)
  have hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G) :=
    fun C h1 h2 h3 h4 => hCN ⟨C, h1, h2, h3, h4⟩
  obtain ⟨hMS, hLcomp, hset, -⟩ := h.toBaum.ms_tail h.hSQ hn1 hRS (F.point_no_strong hR)
    (F.point_hDE hR hJ hJR)
  have hblk := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  exact blockPart_of_hatA6 h.hhat (isHatA6Block_of
    (isHatBlock_of_c132 (card_of_hatA6 h.hhat) hblk))

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
