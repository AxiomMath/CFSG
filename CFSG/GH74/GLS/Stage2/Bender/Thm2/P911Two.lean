module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Glue
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUAlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)

theorem no911_of_fitting {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a)
    (hY : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup (CFSG.generalizedFitting X)],
      (∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a) →
      Nonempty (CFSG.generalizedFitting X ≃* Y) → ∀ t : X, orderOf t = 2 →
        CFSG.oddCore ↥(centralizer ({t} : Set X)) = ⊥) : No911 Y := by
  refine no911_of_oddCore hs hna fun X _ _ S _ hSY hC t ht => ?_
  obtain ⟨ψ⟩ := hSY
  have hSs : IsSimpleGroup S := by
    have := hs
    exact MulEquiv.isSimpleGroup ψ
  have hSna : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨ψ.symm a, ψ.symm b, fun h => hab (by simpa using congrArg ψ h)⟩
  have hF : CFSG.generalizedFitting X = S :=
    Semidihedral.CoreFreeDihedral.generalizedFitting_eq_of_normal_simple_centralizer_eq_bot S
      hSna hC
  have : IsSimpleGroup (CFSG.generalizedFitting X) := by rw [hF]; exact hSs
  refine hY X ?_ ⟨(MulEquiv.subgroupCongr hF).trans ψ⟩ t ht
  obtain ⟨a, b, hab⟩ := hSna
  refine ⟨(MulEquiv.subgroupCongr hF).symm a, (MulEquiv.subgroupCongr hF).symm b, fun h => hab ?_⟩
  simpa using congrArg (MulEquiv.subgroupCongr hF) h

section Two

variable {Y : Type} [Group Y] [Finite Y]

theorem no911_linear_two (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) {f : ℕ} (hf : 3 ≤ f)
    (h : LieModel Y .PSL 2 2 f) : No911 Y := by
  refine no911_of_fitting hs hna fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSL 2 2 f :=
    LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  obtain ⟨-, hiff, -⟩ :=
    ComponentClassification.UnbalancedCatalog.even_linear_two_almost_simple_unbalanced_outcome
      hnonab hmodel
  by_contra hne
  have := ((hiff t ht).mp hne).1
  omega

theorem no911_unitary_three_four (hs : IsSimpleGroup Y) (hna : ∃ a b : Y, a * b ≠ b * a)
    (h : LieModel Y .PSU 3 2 2) : No911 Y := by
  refine no911_of_fitting hs hna fun X _ _ _ hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hmodel : StatedClassicalModel (CFSG.generalizedFitting X) .PSU 3 2 2 :=
    LieType.CurtisTits.statedClassicalModel_of_mulEquiv e.symm
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)
  exact (ComponentClassification.UnbalancedCatalog.even_unitary_almost_simple_odd_core_vanishing
    hnonab hmodel).2 t ht

theorem no911_suzuki_eight (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) (h : LieModel Y .twistedB2 0 2 3) : No911 Y := by
  refine no911_of_fitting hs hna fun X _ _ hsF hnonab hFY t ht => ?_
  obtain ⟨e⟩ := hFY
  have hSz : SuzukiModel Y 2 3 := by
    rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hSz⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact hSz
  have hSzF : SuzukiModel (CFSG.generalizedFitting X) 2 3 := by
    obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := hSz
    exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩
  exact (ComponentClassification.UnbalancedGS.catalog_suzuki_almost_simple_odd_core_vanishing
    hsF hnonab hSzF t ht).2.2

end Two

theorem core911_two : Core911Two := by
  intro Y _ _ hs hna h
  rcases h with h | h | h | h
  · exact no911_linear_two hs hna (f := 3) (by norm_num) h
  · exact no911_linear_two hs hna (f := 4) (by norm_num) h
  · exact no911_unitary_three_four hs hna h
  · exact no911_suzuki_eight hs hna h

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
