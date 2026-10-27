module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOrthLowB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofKleinSixB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddOmegaForms

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KCOrthogonalDescent

theorem orthogonal_component_oddLieCentralQuotient {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : ℕ) (he : 1 ≤ e) (hk : Nat.card k = p ^ e) (Q₀ : QuadraticForm k W)
    (hQ₀ : Q₀.polarBilin.Nondegenerate)
    (M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀)) (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hT : ∃ T : Submodule k W, Module.finrank k T = 3 ∧ ∀ x ∈ T, Q₀ x = 0
  ·
    obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split Q₀ hQ₀
    have hfin := H.finrank_eq
    have hwitt := H.sourceWittIndex_eq hQ₀
    obtain ⟨T, hTd, hTQ⟩ := hT
    have h3 := CFSG.Blueprint.EvenSource.le_sourceWittIndex (K := k) (V := W) (⇑Q₀) (W := T) hTQ
    by_cases h6 : Module.finrank k W = 6
    · exact KleinSix.split_six_component hp hp2 he hk Q₀ hQ₀ h6 ⟨T, hTd, hTQ⟩ hM
    obtain ⟨n, hdim⟩ : ∃ n, (Module.finrank k W = 2 * n + 1 ∧ 3 ≤ n) ∨
        (Module.finrank k W = 2 * n ∧ 4 ≤ n) := by
      rcases Nat.even_or_odd (Module.finrank k W) with ⟨r, hr⟩ | ⟨r, hr⟩
      · exact ⟨r, Or.inr ⟨by omega, by omega⟩⟩
      · exact ⟨r, Or.inl ⟨by omega, by omega⟩⟩
    obtain ⟨hq, τ', n', hadm, hlie⟩ := orthogonal_derived_lieModel hp hp2 he hk Q₀ hQ₀ hdim
    have hMeq := eq_commutator_of_isComponent hq hM
    exact ⟨τ', n', e, hadm, LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hMeq.symm)
        (Subgroup.map_center_eq _)) hlie⟩
  ·
    have hle := CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three hodd Q₀ hQ₀ hT
    by_cases hsmall : Module.finrank k W ≤ 2
    · have := CatalogueBOrthogonal.orthogonal_small_solvable Q₀ h2 hQ₀ hsmall
      exact (not_isComponent_of_isSolvable hM).elim
    rcases (show Module.finrank k W = 3 ∨ Module.finrank k W = 4 ∨ Module.finrank k W = 5 ∨
        Module.finrank k W = 6 by omega) with h | h | h | h
    · exact orthogonal_three_component_oddLieCentralQuotient hp hp2 he hk Q₀ hQ₀ h hM
    · by_cases hS : ∃ S : Submodule k W, Module.finrank k S = 2 ∧ ∀ x ∈ S, Q₀ x = 0
      · exact orthogonal_split_four_component_oddLieCentralQuotient hp hp2 he hk Q₀ hQ₀ h hS hM
      · exact orthogonal_nonsplit_four_component_oddLieCentralQuotient hp hp2 he hk Q₀ hQ₀ h hS
          hM
    · exact orthogonal_five_component_oddLieCentralQuotient hp hp2 he hk Q₀ hQ₀ h hM
    · exact orthogonal_nonsplit_six_component_oddLieCentralQuotient hp hp2 he hk Q₀ hQ₀ h hT hM

theorem orthogonalComponentsLie_holds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (e : ℕ), 1 ≤ e → Nat.card k = p ^ e → ∀ Q₀ : QuadraticForm k W,
      Q₀.polarBilin.Nondegenerate → 3 ≤ Module.finrank k W →
      ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀), IsComponent M →
        OddLieCentralQuotient p M :=
  fun k W _ _ _ _ _ e he hk Q₀ hQ₀ _ M hM =>
    orthogonal_component_oddLieCentralQuotient hp hp2 k W e he hk Q₀ hQ₀ M hM

end CFSG.ComponentClassification.CatLeafProof
