module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSeven
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSix
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

theorem statedClassicalModel_psl_two_four_of_alternating_five
    (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) : StatedClassicalModel X .PSL 2 2 2 := by
  obtain ⟨e⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hcard]; norm_num))
  exact ⟨⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩, GaloisField 2 2,
    inferInstance, inferInstance, hcard, ⟨e.trans e5.symm⟩⟩

theorem statedClassicalModel_psl_four_two_of_alternating_eight (X : Type) [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 8))) : StatedClassicalModel X .PSL 4 2 1 := by
  rcases (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).mpr h with
    ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact hc
  all_goals exact absurd ht (by decide)

theorem sqtkCharTwoLie_of_alternating_five {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 5))) : SQTKCharTwoLie X :=
  Or.inl (Or.inl ⟨2, Or.inl ⟨le_rfl, statedClassicalModel_psl_two_four_of_alternating_five X h⟩⟩)

theorem sqtkCharTwoLie_of_alternating_eight {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 8))) : SQTKCharTwoLie X :=
  Or.inr ⟨4, Or.inl rfl, statedClassicalModel_psl_four_two_of_alternating_eight X h⟩

theorem simpleInspection_altList
    (hE : EvenLieAutInner) : SimpleInspection AltList := by
  intro K _ _ β h hz ⟨n, h5, h8, ⟨e⟩⟩
  obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  · exact simpleInspection_charTwoList hE K β h hz (sqtkCharTwoLie_of_alternating_five ⟨e⟩)
  · exact simpleInspection_altSix K β h hz ⟨e⟩
  · exact simpleInspection_altSeven K β h hz ⟨e⟩
  · exact simpleInspection_charTwoList hE K β h hz (sqtkCharTwoLie_of_alternating_eight ⟨e⟩)

end CFSG.QuasithinUnique.Ch1
