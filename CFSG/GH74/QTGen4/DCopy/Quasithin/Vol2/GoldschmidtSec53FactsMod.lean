module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.GoldschmidtSec53FactsLoc
public import CFSG.Quasithin.Background.F1AmalgamRestrict
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsAm

public section

namespace CFSG.Quasithin.H13.Sec53F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F1

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n : ℕ}
  {P : Type} [Group P] [CFSG.GH74.QTGen4.Finite4 P] {N₁ N₂ : Subgroup P}
  (Φ : (RankTwoAmalgam.ofSubgroups (fG1 M L H B) (fG2 M L H D)).Iso
    (RankTwoAmalgam.ofSubgroups N₁ N₂))

theorem sec53S_le_K_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n) :
    sec53S T L ≤ oTwoUpper H := by
  obtain ⟨-, ⟨-, -, -, hST, hSK, -⟩, -⟩ := h527 G T M L V H B D L₂ n hyp
  rw [show sec53S T L = T ⊓ L from rfl, ← hST, hSK]
  exact inf_le_right

omit [CFSG.GH74.QTGen4.Finite4 P] in

theorem mem_S_iff_F4 (h527 : Stmt5_2_7_F4) (hyp : Hyp5_2_4 G T M L V H B D L₂ n)
    (x : ↥(fG1 M L H B ⊓ fG2 M L H D)) :
    (x : G) ∈ sec53S T L ↔ ((isoφ12 Φ x : ↥(N₁ ⊓ N₂)) : P) ∈ pCoreOf 2 (N₁ ⊓ N₂) := by
  rw [← pCoreOf_fG12_F4 h527 hyp, mem_pCoreOf_iff_of_equiv (isoφ12 Φ) x]

end CFSG.Quasithin.H13.Sec53F
