module

public import CFSG.Quasithin.H13.FiveMenu
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped IsMulCommutative

theorem five_selected_action_menu_producer_F4
    (h1222 : Stmt12_2_2_F4) : StmtFiveSelectedMenu_F4 := by
  intro G _ _ T L hs hnab hQ hT hnex hmax hf hq
  rcases h1222 G T hs hnab hQ hT with hA | h3
  · exact absurd (qt13Excluded_of_alt12_2_2 hA) hnex
  obtain ⟨-, ⟨V, hV⟩, hall⟩ := h3 L hmax hf hq
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hcomm, hmod⟩ := hall V hV
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have helem : IsElemAbelian 2 V := by
    refine ⟨hcomm, fun x hx => ?_⟩
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (L ⊔ T))
      (⟨x, hVLT hx⟩ : ↥(L ⊔ T)) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | ⟨-, -, hA6, -⟩
  · exact Or.inl ⟨n, hn, lieModel_psl_of_mulEquiv_sl_zmod_two (by omega) e⟩
  · exact Or.inl ⟨3, Or.inl rfl, lieModel_psl_of_mulEquiv_sl_zmod_two le_rfl e⟩
  · exact Or.inl ⟨5, Or.inr (Or.inr rfl), lieModel_psl_of_mulEquiv_sl_zmod_two (by norm_num) e⟩
  · obtain ⟨hO2, hlt⟩ := pCoreOf_le_inf_centralizer_of_surjective hn5 φ hφ hker
    exact Or.inr (Or.inr (Or.inr ⟨n, hn5, hn8, V, hV.2.1, helem, hV.2.2.1, hO2, hlt, φ, hφ,
      hker⟩))
  · obtain ⟨hO2, hlt⟩ := pCoreOf_le_inf_centralizer_of_surjective (by norm_num) φ hφ hker
    exact Or.inr (Or.inr (Or.inr ⟨7, by norm_num, by norm_num, V, hV.2.1, helem, hV.2.2.1, hO2,
      hlt, φ, hφ, hker⟩))
  · exact Or.inr (Or.inl (exists_mulEquiv_g2Derived_of_lieModel hU))
  · exact Or.inr (Or.inr (Or.inl hA6))

theorem five_action_menu_to_candidate_quotients_F4 (hmenu : StmtFiveSelectedMenu_F4) :
    StmtFiveCandidateMenu_F4 := by
  intro G _ _ T L hs hnab hQ hT hnex hmax hf hq
  rcases hmenu G T L hs hnab hQ hT hnex hmax hf hq with ⟨n, hn, h⟩ | ⟨K, _, hK, e⟩ | hA6 |
      ⟨n, hn5, hn8, V, -, -, -, -, -, φ, hφ, -⟩
  · exact Or.inl ⟨n, hn, h⟩
  · exact Or.inr (Or.inl ⟨K, inferInstance, hK, e⟩)
  · exact Or.inr (Or.inr ⟨6, by norm_num, by norm_num, hA6⟩)
  · have hle := pCore_le_ker_of_surjective_alternating hn5 φ hφ
    have : IsSimpleGroup (alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
    obtain ⟨-, e, -⟩ := SteinbergBM.five_quasisimple_centerless_image hq
      (alternatingGroup_nonabelian (by omega)) (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
    exact Or.inr (Or.inr ⟨n, hn5, hn8, ⟨e⟩⟩)

end CFSG.Quasithin.H13
