module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpArms
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.HNCenter

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder)

theorem rows_hs_only_hn (s' : TauCeti.SporadicName) (h : sporOrder .HS ∣ AGLEmbedding.sporOrd s') :
    (SporadicInnerRow s' (sporOrder .HS) → s' = .HN) ∧ ¬ SporadicOuterRow s' (sporOrder .HS) := by
  rw [sporOrder_eq_sporOrd] at h ⊢
  cases s' <;> first
    | exact absurd h (by simp only [AGLEmbedding.sporOrd]; decide)
    | (simp only [SporadicInnerRow, SporadicOuterRow, AGLEmbedding.sporOrd] <;> decide)

variable {S : Type} [Group S] [Finite S]

section HNInner


theorem clause3_of_inputs (I : ArmInputs) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) (hHS : IsSporadic (↥D ⧸ center ↥D) .HS) :
    IsSporadic S .HN ∧ Nat.card (center ↥D) = 2 := by
  obtain ⟨g⟩ := hHS
  have hc : Nat.card (↥D ⧸ center ↥D) = sporOrder .HS := by
    rw [Nat.card_congr g.toEquiv, I.card .HS (by decide)]
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, hDk⟩ | ⟨hodd, -⟩ | ⟨heven, -⟩ | ⟨s', ⟨es⟩⟩
  · exact (not_alt_of_sporOrder (a := 11) (by omega) hc
      (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial])
      (by simp only [AGLEmbedding.sporOrd]; norm_num [Nat.factorial]) hDk).elim
  · exact (false_of_oddLie_fixedComponent I.gls I.order hodd hσ hD hc).elim
  · have hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ},
        StatedLieAdmissible t n 2 f → LieModel X t n 2 f → Nat.card X ≠ sporOrder .HS := by
      intro X _ t n f hadm hX
      rw [sporOrder_eq_sporOrd]
      exact lieModel_two_card_ne_hs I.order hadm hX
    exact (false_of_evenLie_fixedComponent I.evenInner I.evenOuter I.order hna heven hσ hD hc
      hne2).elim
  · obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hc] at hdvd hin hout
    obtain ⟨hinHN, hnotout⟩ := rows_hs_only_hn s' hdvd
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain rfl := hinHN (hin hinn)
      exact ⟨⟨es⟩, hn_inner_component_center ‹IsSimpleGroup S› hna es hσ hinn hD⟩
    · exact (hnotout (hout hinn)).elim

end HNInner

end CFSG.ComponentClassification.CatFC
