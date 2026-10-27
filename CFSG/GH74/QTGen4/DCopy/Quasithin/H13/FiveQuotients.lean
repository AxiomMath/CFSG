module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.FiveMenu
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.LinearSelected
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Statements
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.Quasithin.H13.FiveAltCover
public import CFSG.Quasithin.SteinbergBMCoreQuotientCenterOdd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def StmtFiveA7Elim_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      ¬ Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 7))

theorem residual_maximal_quasisimple_five_quotients_F4
    (hcand : StmtFiveCandidateMenu_F4)
    (hA7 : StmtFiveA7Elim_F4) (hprod : LinearSelectedNaturalConfigurationProducer_F4) :
    Stmt13_1_2_three_F4 := by
  intro G _ _ T L hs hnab hQ hT hnex hmax hf hq
  obtain ⟨-, -, hodd⟩ := SteinbergBM.five_core_quotient_center_odd hq
  have hlin' :=
    five_large_linear_local_quotient_elimination_F4 hprod G T L hs hnab hQ hT hnex hmax hf hq
  rcases hcand G T L hs hnab hQ hT hnex hmax hf hq with ⟨n, hn, h⟩ | ⟨K, _, hK, ⟨e⟩⟩ |
      ⟨n, hn5, hn8, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (Or.inl h)
    · exact absurd h hlin'.1
    · exact absurd h hlin'.2
  · have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
    exact Or.inr (Or.inr (Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv e.symm
      (EmptyFaithfulMultiple.g2TwoDerivedUnitaryTransport_holds K hK)))))
  · have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    obtain ⟨h58, -, h56⟩ := five_alternating_small_central_cover_reduction hq hodd hn' e
    rcases hn' with rfl | rfl | rfl | rfl
    · exact h56 (Or.inl rfl)
    · exact h56 (Or.inr rfl)
    · exact absurd ⟨e⟩ (hA7 G T L hs hnab hQ hT hnex hmax hf hq)
    · exact absurd ((ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2
        (h58 (Or.inr rfl)).2) hlin'.1

theorem stmt13_1_2_three_of_inputs_F4
    (h1222 : Stmt12_2_2_F4) (hA7 : StmtFiveA7Elim_F4)
    (hprod : LinearSelectedNaturalConfigurationProducer_F4) : Stmt13_1_2_three_F4 :=
  residual_maximal_quasisimple_five_quotients_F4
    (five_action_menu_to_candidate_quotients_F4 (five_selected_action_menu_producer_F4 h1222)) hA7 hprod

end CFSG.Quasithin.H13
