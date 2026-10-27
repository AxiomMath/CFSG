module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35EL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL35ESporFact
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECExc
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECO82
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsECMult

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts CFSG.Assembly.LowTwoRank

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem even_concl
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hGA : TBLit.GriessMultipliersAllModels)
    (h : Config G p w v L K) (halt : ¬ N36.IsAlt (↥K ⧸ Open.fusionZStar ↥K)) {t : StatedLieTag}
    {n f : ℕ} (hL : Blueprint.LieModel (↥K ⧸ Open.fusionZStar ↥K) t n 2 f) : Concl p v L K := by
  obtain ⟨eZ⟩ := h.nonempty_bar_equiv
  have hmS : Blueprint.LieModel ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) t n 2 f :=
    GSThmB.OddQuot.lieModel_of_equiv eZ hL
  have hout := h.even_not_inner hmS
  have h12 := EvenCover.twelve_of_even_center hGA h.quasisimple_quot hmS
    (even_iff_two_dvd.mp h.even_card_center)
  have key : EvenCover.NoOddPSL2 ((↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) →
      False := fun hY => h.even_false_of_noOddPSL2 hY hout
  unfold EvenCover.IsTwelve at h12
  rcases h12 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact (halt ⟨5, le_rfl,
      LocalAnalysis.ComponentInitial.PSL2_four_alternating_five_model _ hL⟩).elim
  · exact (h.even_false_of_oddModel hGLS hGA (by norm_num : 7 ≠ 2)
      (LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hL)).elim
  · exact (halt ⟨8, by norm_num, (SymmetricLocal.lie_model_linear_four_two_iff _).mp hL⟩).elim
  · exact (h.even_false_of_oddModel hGLS hGA (by norm_num : 3 ≠ 2)
      (GH74.Exceptional.lieModel_PSp_two_three_of_lieModel_PSU_four_two hL)).elim
  · exact (key (EvenCover.noOddPSL2_Sp62 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_G2 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_F4 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_O82 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_U62 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_Sz8 hmS)).elim
  · exact (key (EvenCover.noOddPSL2_twistedE6 hmS)).elim
  · exact h.even_concl_of_L34 hmS hout

end Config

end CFSG.ComponentClassification.HarrisLit.L35

namespace CFSG.ComponentClassification.HarrisLit

theorem harris81Lemma35IdentEvenSporFact_of_spor
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hS : Harris81Lemma35IdentSporFact) : Harris81Lemma35IdentEvenSporFact := by
  intro G _ _ p w v L K h halt hcase
  rcases hcase with ⟨t, n, f, hL⟩ | hspor
  · exact h.even_concl hGLS hGA halt hL
  · exact hS G p w v L K h halt hspor

end CFSG.ComponentClassification.HarrisLit
