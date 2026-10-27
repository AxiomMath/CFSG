module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Cor332
public import CFSG.Quasithin.Vol2.Ch3Sec3Setup

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt3_3_1A_of_false_F4
    (h : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D → False) :
    Stmt3_3_1A_F4 := by
  intro G _ _ T hs hnab hK hT M L hM hTM hL hLM hq
  by_contra hc
  obtain ⟨D, hD⟩ := exists_hyp331 ⟨hs, hnab, hK, hT, hM, hTM, hL, hLM, hq⟩ hc
  exact h G T M L D hD

end CFSG.Quasithin.H13
