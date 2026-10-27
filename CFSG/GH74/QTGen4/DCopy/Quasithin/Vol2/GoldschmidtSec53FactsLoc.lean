module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsLoc
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Statements

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}

theorem fG1_eq_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG1 M L H B = L ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨e1, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, e1, sup_assoc]

theorem fG2_eq_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG2 M L H D = oTwoUpper H ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨-, e2, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG2, e2, sup_assoc]

theorem fG12_eq_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    fG1 M L H B ⊓ fG2 M L H D = sec53S T L ⊔ (B ⊔ D) := by
  obtain ⟨-, ⟨e1, e2, e3, hST, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, fG2, e1, e2, e3, hST, sup_assoc]

theorem pCoreOf_fG12_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    pCoreOf 2 (fG1 M L H B ⊓ fG2 M L H D) = sec53S T L := by
  obtain ⟨-, ⟨e1, e2, -, hST, -, hO2⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [fG1, fG2, e1, e2, ← hO2, hST]

theorem sec53S_le_fG12_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ fG1 M L H B ⊓ fG2 M L H D := by
  rw [← pCoreOf_fG12_F4 h527 hyp]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

end CFSG.Quasithin.H13.Sec53F
