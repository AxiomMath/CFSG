module

public import CFSG.Quasithin.H13.A7Elimination
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A7EscapeProducer
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.FiveQuotients
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec4Statements

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

@[expose] def StmtA7FinalModuleWitness_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → ¬ QT13Excluded G →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ (U K D : Subgroup G) (v : G), IsElemAbelian 2 U ∧
      K ≤ normalizer (U : Set G) ∧ D ≤ normalizer (U : Set G) ∧ v ≠ 1 ∧ v ∈ ⁅U, D⁆ ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ⁅K, D⁆ ≤ centralizer (U : Set G) ∧
      ⁅U, K⁆ ⊓ ⁅U, D⁆ = ⊥ ∧ centralizer ({v} : Set G) ≤ normalizer (L : Set G)

theorem A7_final_module_witness_producer_F4 (hesc : StmtA7EscapingLocalActionData_F4) :
    StmtA7FinalModuleWitness_F4 :=
  fun G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7 =>
    A7_final_module_witness_of_data hQTKE hT (hesc G T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7)

theorem five_A7_local_quotient_elimination_F4 (hW : StmtA7FinalModuleWitness_F4) : StmtFiveA7Elim_F4 :=
  fun G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7 =>
    false_of_A7_final_module_witness (hW G T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7)

theorem stmtFiveA7Elim_of_inputs_F4
    (hG10 : StmtA7NaturalModuleConfig_F4) (h12213 : Stmt12_2_13_F4)
    (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) (h331 : Stmt3_3_1_F4) :
    StmtFiveA7Elim_F4 :=
  five_A7_local_quotient_elimination_F4 (A7_final_module_witness_producer_F4
    (A7_escaping_local_action_data_producer_F4 hG10 h12213 h1227 h1228 h1229 h331))

@[expose] def StmtA7NaturalModuleConfigHyp_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G), Hyp1223 G T L V →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      alternatingGroup (Fin 7)) →
    ∃ ψ : V ≃* Multiplicative (evenWeight 7), A7NatConfig T L V ψ

theorem stmtA7NaturalModuleConfig_of_hyp_F4 (h1222 : Stmt12_2_2_F4)
    (hG10 : StmtA7NaturalModuleConfigHyp_F4) : StmtA7NaturalModuleConfig_F4 := by
  intro G _ _ T L hs hnab hQTKE hT hnex hLmax hLf hLq hA7
  have hnalt : ¬ Alt12_2_2 G := fun h' => hnex (qt13Excluded_of_alt12_2_2 h')
  rcases h1222 G T hs hnab hQTKE hT with hAlt | h3
  · exact absurd hAlt hnalt
  obtain ⟨hTL, ⟨V, hV⟩, -⟩ := h3 L hLmax hLf hLq
  obtain ⟨ψ, hψ⟩ := hG10 G T L V ⟨hs, hnab, hQTKE, hT, hnalt, hLmax, hLf, hLq, hTL, hV⟩ hA7
  exact ⟨V, ψ, hψ⟩

theorem stmt12_3_1_of_inputs_F4
    (hG10 : StmtA7NaturalModuleConfigHyp_F4) (h12213 : Stmt12_2_13_F4)
    (h1227 : Stmt12_2_7_F4) (h1228 : Stmt12_2_8_F4) (h1229 : Stmt12_2_9_F4) (h331 : Stmt3_3_1_F4) :
    Stmt12_3_1_F4 := by
  intro G _ _ T L V hyp hA7
  obtain ⟨ψ, hcfg⟩ := hG10 G T L V hyp hA7
  exact false_of_A7_final_module_witness (A7_final_module_witness_of_data hyp.qtke hyp.sylow
    (A7_escaping_local_action_data_of_hyp1223_F4 h12213 h1227 h1228 h1229 h331 hyp hcfg hA7))

end CFSG.Quasithin.H13.A7
