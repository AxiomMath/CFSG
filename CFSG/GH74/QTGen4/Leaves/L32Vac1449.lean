module

public import CFSG.GH74.QTGen4.L32.Gen4Cuts
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems144d

public section

namespace CFSG.GH74.QTGen4

open CFSG.GH74 CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Open

theorem not_case1442Three_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T V V₂ : Subgroup G} {g : G} (D : HatModelU (fsuU T V)) : ¬ Case1442Three T V V₂ g D := by
  rintro ⟨e, -⟩
  have h := finrank_hatModel_le_four hG D
  have h8 := LinearEquiv.finrank_eq e
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h8
  omega

theorem lemma1449Big_F4_holds : Lemma1449Big_F4 := by
  intro G _ _ T L V _ _ _ V₂ g _ _ _ D
  exact not_case1442Three_gen4 (Finite4.gen4) D

theorem lemma14410A5_F4_holds : Lemma14410A5_F4 := by
  intro G _ _ T L V _ _ _ V₂ g _ _ _ D b₁ e _ _
  have h := finrank_hatModel_le_four (Finite4.gen4 (G := G)) D
  have h8 := LinearEquiv.finrank_eq e
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h8
  omega

end CFSG.GH74.QTGen4
