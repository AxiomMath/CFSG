module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.CentrePLSplit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NineThreeCentreDispatch
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.NineThreeTwoSmall

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def IsClassicalOrG2ResidualQuotient (Q : Type) [Group Q] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 ∧ ¬ IsClassicalOrG2IndexTwo d.1 ∧
    Nonempty (Q ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def NineThreeTwoResidue : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeTwo M S L → ¬ IsSylowTwoOf (barM M (S ⊓ L)) (barM M L) → BlockPLThreeSolv M S L →
    IsClassicalOrG2ResidualQuotient (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ¬ 9 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _)

theorem kFactBlockCentreNine_of_residue
    (hG : GriessAllModelsStatement) (hR : NineThreeTwoResidue) : KFactBlockCentreNine := by
  intro G _ _ M S L hL hconc hnot hSyl hsolv hZ
  have hperf : Group.IsPerfect ↥(barM M L) := ⟨hL.component.2.2.1⟩
  rcases hconc with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact absurd h1 hnot
  · rcases h2.1 with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
    · by_cases h2d : IsClassicalOrG2IndexTwo d.1
      · exact not_nine_dvd_barM_inf_centralizer_of_small_nineThreeTwo hG M L hperf
          (Or.inl ⟨d, h2d, ⟨e⟩⟩)
      · exact hR G M S L hL h2 (hSyl h2) hsolv ⟨d, hd, h2d, ⟨e⟩⟩ hZ
    · exact not_nine_dvd_barM_inf_centralizer_of_small_nineThreeTwo hG M L hperf
        (Or.inr (Or.inl ⟨n, hn, ⟨e⟩⟩))
    · rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
      · exact not_nine_dvd_barM_inf_centralizer_of_small_nineThreeTwo hG M L hperf
          (Or.inr (Or.inr (Or.inl ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩)))
      · exact not_nine_dvd_barM_inf_centralizer_of_small_nineThreeTwo hG M L hperf
          (Or.inr (Or.inr (Or.inr ⟨d, ⟨q, hq, hdq⟩, ⟨e⟩⟩)))
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL (Or.inl h3)
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL (Or.inr (Or.inl h4))
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL
      (Or.inr (Or.inr (Or.inl h5)))
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL
      (Or.inr (Or.inr (Or.inr (Or.inl h6))))
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h7)))))
  · exact not_nine_dvd_barM_inf_centralizer_of_outcome_three_to_eight hL
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h8)))))

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
