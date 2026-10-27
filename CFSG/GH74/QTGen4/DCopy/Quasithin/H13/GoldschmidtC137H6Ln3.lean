module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.H13.GoldschmidtC137H6Blk
public import CFSG.Quasithin.H13.GoldschmidtC137H6Ln2
public import CFSG.Quasithin.H13.GoldschmidtC137TailW

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [CFSG.GH74.QTGen4.Finite4 G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem line_block_F4 (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32_F4)
    (hCN : ¬ CharNormal (baum (pCoreOf 2 P)) X) (hP : autI h.hVe P = H2.map F.ρ)
    (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) : BlockPart L := by
  have hJ1 := F.line_J_eq hP hR h5 hJ
  have hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)) := by
    rw [hR, ← hJ1]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)
  have hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G) :=
    fun C h1 h2 h3 h4 => hCN ⟨C, h1, h2, h3, h4⟩
  obtain ⟨hMS, hLcomp, hset, -⟩ := h.toBaum.ms_tail' h.hSQ hn1 hRS (F.line_no_strong hR h5)
    (F.line_hDE hP hR h5 hJ)
  have hblk := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  exact blockPart_of_hatA6 h.hhat (isHatA6Block_of
    (isHatBlock_of_c132 (card_of_hatA6 h.hhat) hblk))

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
