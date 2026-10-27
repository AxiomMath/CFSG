module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.ExistsIrrational
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.ExistsIrrationalF4
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.FieldTwo
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.Residuals
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.TwistedE6

open CFSG.LieType.SeitzGeneration
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

theorem subfieldMaximalAllOdd_of_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    SubfieldMaximalAllOdd τ := by
  intro K _ _ σ p hp hp2 hpK hσ M hRM
  by_cases hk2 : Nat.card (fixSubfield σ) = 2
  · exact subfieldMaximal_of_card_two (Or.inr hτ) σ hp hp2 hσ hpK hk2 M hRM
  have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
    by_cases h2 : ringChar K = 2
    · exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd σ h2).resolve_left hk2)
    · exact Or.inl h2
  by_cases hM : M = subfieldGroup τ σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup τ σ := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  obtain ⟨r, hr, r', hr', γ, hγ, t, ht, hmem⟩ :=
    exists_irrational_rootElt_of_not_mem hτ σ hp hp2 hσ hpK hD g hgR
  set H := Subgroup.closure ((subfieldGroup τ σ : Set ↥(adjointGroup τ K)) ∪
    ((subfieldGroup τ σ).map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup τ K)))
    with hH
  have hgg : r * g * r' ∈ M := mul_mem (mul_mem (hRM hr) hgM) (hRM hr')
  have hHM : H ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hRM hx
    · exact M.mul_mem (M.mul_mem hgg (hRM hy)) (M.inv_mem hgg)
  have hRH : ∀ γ, IsRoot τ γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily τ) γ c ∈ H := fun γ _ c hc =>
    Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup τ σ γ hc))
  have hHtop : H = ⊤ := eq_top_of_irrational_rootElt hτ (fixSubfield σ)
    (fun F hF => subfield_eq_or_top σ hp hσ F hF) H hRH γ hγ t ht hmem
  exact eq_top_iff.2 (hHtop ▸ hHM)

theorem subfieldMaximalAll_of_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    SubfieldMaximalAll τ :=
  (subfieldMaximalAllOdd_of_E τ hτ).toAll

theorem subfieldMaximalAllThree_of_E (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    SubfieldMaximalAllThree τ :=
  (subfieldMaximalAllOdd_of_E τ hτ).toThree

theorem subfieldMaximalAllOdd_F4 : SubfieldMaximalAllOdd .F4 := by
  intro K _ _ σ p hp hp2 hpK hσ M hRM
  by_cases hk2 : Nat.card (fixSubfield σ) = 2
  · exact subfieldMaximal_of_card_two (Or.inl rfl) σ hp hp2 hσ hpK hk2 M hRM
  have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
    by_cases h2 : ringChar K = 2
    · exact Or.inr ((card_fixSubfield_eq_two_or_four_dvd σ h2).resolve_left hk2)
    · exact Or.inl h2
  by_cases hM : M = subfieldGroup .F4 σ
  · exact Or.inl hM
  right
  obtain ⟨g, hgM, hgR⟩ : ∃ g ∈ M, g ∉ subfieldGroup .F4 σ := by
    by_contra h
    push Not at h
    exact hM (le_antisymm (fun g hg => h g hg) hRM)
  obtain ⟨r, hr, r', hr', γ, hγ, t, ht, hmem⟩ :=
    exists_irrational_longRootElt_of_not_mem σ hp hp2 hσ hpK hD g hgR
  set H := Subgroup.closure ((subfieldGroup .F4 σ : Set ↥(adjointGroup .F4 K)) ∪
    ((subfieldGroup .F4 σ).map (MulAut.conj (r * g * r')).toMonoidHom : Set ↥(adjointGroup .F4 K)))
    with hH
  have hgg : r * g * r' ∈ M := mul_mem (mul_mem (hRM hr) hgM) (hRM hr')
  have hHM : H ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hRM hx
    · exact M.mul_mem (M.mul_mem hgg (hRM hy)) (M.inv_mem hgg)
  have hRH : ∀ γ, IsRoot .F4 γ → ∀ c ∈ fixSubfield σ,
      xPar (rootOperatorFamily .F4) γ c ∈ H := fun γ _ c hc =>
    Subgroup.subset_closure (Or.inl (xPar_mem_subfieldGroup .F4 σ γ hc))
  have hHtop : H = ⊤ := eq_top_of_irrational_longRootElt (fixSubfield σ)
    (fun F hF => subfield_eq_or_top σ hp hσ F hF) H hRH γ hγ t ht hmem
  exact eq_top_iff.2 (hHtop ▸ hHM)

theorem subfieldMaximalAll_F4 : SubfieldMaximalAll .F4 := subfieldMaximalAllOdd_F4.toAll

theorem subfieldMaximalAll_E6 : SubfieldMaximalAll .E6 := subfieldMaximalAll_of_E .E6 (Or.inl rfl)

theorem subfieldMaximalAll_E7 : SubfieldMaximalAll .E7 := subfieldMaximalAll_of_E .E7 (Or.inr (Or.inl rfl))

theorem subfieldMaximalAll_E8 : SubfieldMaximalAll .E8 := subfieldMaximalAll_of_E .E8 (Or.inr (Or.inr rfl))

theorem subfieldMaximalAllThree_E6 : SubfieldMaximalAllThree .E6 := subfieldMaximalAllThree_of_E .E6 (Or.inl rfl)

theorem subfieldMaximalLeOne_F4 : SubfieldMaximalLeOne .F4 := subfieldMaximalAll_F4.toLeOne

theorem subfieldMaximalLeOne_E6 : SubfieldMaximalLeOne .E6 := subfieldMaximalAll_E6.toLeOne

theorem subfieldMaximalLeOne_E7 : SubfieldMaximalLeOne .E7 := subfieldMaximalAll_E7.toLeOne

theorem subfieldMaximalLeOne_E8 : SubfieldMaximalLeOne .E8 := subfieldMaximalAll_E8.toLeOne

theorem excOuterLeOne_fields :
    SeitzExcOuterNarrowF4LeOne ∧ SeitzExcOuterNarrowE6LeOne ∧ SeitzExcOuterNarrowE7LeOne ∧
      SeitzExcOuterNarrowE8LeOne ∧ SeitzExcOuterNarrowTwistedE6LeOne :=
  ⟨seitzExcOuterNarrowF4LeOne_of_maximal subfieldMaximalLeOne_F4,
    seitzExcOuterNarrowE6LeOne_of_maximal subfieldMaximalLeOne_E6,
    seitzExcOuterNarrowE7LeOne_of_maximal subfieldMaximalLeOne_E7,
    seitzExcOuterNarrowE8LeOne_of_maximal subfieldMaximalLeOne_E8,
    seitzExcOuterNarrowTwistedE6LeOne_of_maximal subfieldMaximalLeOneTwE6⟩

theorem seitzExcOuterCycResiduals_of_core :
    CFSG.AGLEmbedding.SeitzCyc.SeitzExcOuterCycResiduals :=
  seitzExcOuterCycResiduals_of_maximal subfieldMaximalLeOne_F4 subfieldMaximalLeOne_E6
    subfieldMaximalLeOne_E7 subfieldMaximalLeOne_E8 subfieldMaximalLeOneTwE6

theorem fieldAutData_F4_of_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ≠ ringChar K) : CFSG.RankThree.PartOne.CTP.FieldAutData (adjointGroup Tag.F4 K) p :=
  fieldAutData_F4_of_subfieldMaximalAllOdd subfieldMaximalAllOdd_F4 hp hp2 hpK

theorem fieldAutData_E7_of_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ≠ ringChar K) : CFSG.RankThree.PartOne.CTP.FieldAutData (adjointGroup Tag.E7 K) p :=
  fieldAutData_E7_of_subfieldMaximalAllOdd (subfieldMaximalAllOdd_of_E .E7 (Or.inr (Or.inl rfl))) hp hp2
    hpK

theorem fieldAutData_E8_of_odd {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ≠ ringChar K) : CFSG.RankThree.PartOne.CTP.FieldAutData (adjointGroup Tag.E8 K) p :=
  fieldAutData_E8_of_subfieldMaximalAllOdd (subfieldMaximalAllOdd_of_E .E8 (Or.inr (Or.inr rfl))) hp hp2
    hpK

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
