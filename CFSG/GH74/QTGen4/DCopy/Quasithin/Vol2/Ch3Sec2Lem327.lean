module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem327

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem isTISetUnder_of_stmt3_2_5_F4 (h325 : Stmt3_2_5_F4) {T L V₀ : Subgroup G}
    (hfsu : FSU G T L V₀) (hL : L = conjClosure L T) :
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL
  rw [← hL]
  rcases hcases with ⟨-, hVM⟩ | ⟨hV, -, -, -, hTI⟩ | ⟨-, -, ⟨t, ht, htN⟩, hall⟩
  · exact isTISetUnder_of_eq_conjClosure hVM
  · rw [← hV]
    exact hTI
  · exact isTISetUnder_of_eq_conjClosure (hall t ht htN).1.symm

end CFSG.Quasithin.H13
