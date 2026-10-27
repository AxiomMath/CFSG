module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreRestr
public import CFSG.ClassicalInvolution.Q3.LieDecomposition
public import CFSG.ClassicalInvolution.Uniform.U3Edge
public import CFSG.ClassicalInvolution.Uniform.ULieType

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section System

variable {p f : ℕ} [Fact p.Prime] {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}


theorem subsingleton_of_noCommute (D : LieSystemDataU p f ι X Φ)
    (hno : ∀ A ∈ Φ, ∀ B ∈ Φ, ¬ Commutes A B) : Subsingleton ι := by
  refine ⟨fun i j => ?_⟩
  by_contra hij
  obtain ⟨R, -, hR⟩ := D.meets i
  obtain ⟨S, -, hS⟩ := D.meets j
  refine hno _ hR _ hS ?_
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩
  exact D.commute i j hij a b

theorem lieSystemDataU_surjective_hom [Subsingleton ι] (D : LieSystemDataU p f ι X Φ) (i : ι) :
    Function.Surjective (D.hom i) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← D.generate]
  exact iSup_le fun j => by rw [Subsingleton.elim j i]

theorem top_mem_of_sl23 [Subsingleton ι] (D : LieSystemDataU p f ι X Φ) (i : ι)
    (hc : D.kind i = Q3.CompData.sl23) : (⊤ : Subgroup X) ∈ Φ := by
  obtain ⟨R, hR, hmem⟩ := D.meets i
  have hRtop : R = ⊤ := Q3.fund_eq_top_of_sl23 hc R hR
  have : R.map (D.hom i) = ⊤ := by
    rw [hRtop, Subgroup.map_top, MonoidHom.range_eq_top.mpr (lieSystemDataU_surjective_hom D i)]
  rwa [this] at hmem

end System

section SectionSystem


variable {Y₀ : Type} [Group Y₀] [Finite Y₀] {Λ₀ : Set (Subgroup Y₀)}

theorem lieSystemU_section {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card Y₀ < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) :
    LieSystemU 3 1 (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))
      (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :=
  (hIH ↥(omegaGen Λ₀) ((Subgroup.card_le_card_group _).trans_lt hn) _
    (inClassU_restrict_omegaGen hΩ hne)).toLieSystemU

theorem sectionFamily_nonempty (hne : Λ₀.Nonempty) :
    (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))).Nonempty := by
  obtain ⟨K, hK⟩ := hne
  exact ⟨_, ⟨K.subgroupOf (omegaGen Λ₀), ⟨K, hK, le_omegaGen hK, rfl⟩, rfl⟩⟩

theorem sectionThm6U_exists_system {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card Y₀ < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀) :
    Nonempty (LieSystemDataU 3 1 (Fin 1)
      (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))
      (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀)))) := by
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemU_section hIH hn hΩ hne
  have hsub : Subsingleton ι := subsingleton_of_noCommute D fun A hA B hB h =>
    false_of_commutes_in_section hΩ hDE hA hB h
  obtain ⟨L, hL⟩ := sectionFamily_nonempty hne
  obtain ⟨i, -⟩ := D.fundamental L hL
  have : Unique ι := uniqueOfSubsingleton i
  exact ⟨D.reindex (Equiv.ofUnique (Fin 1) ι)⟩

end SectionSystem

section Model


variable {p f : ℕ} [Fact p.Prime] {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] noncomputable def ih8ModelOfSystemU [Subsingleton ι]
    (D : LieSystemDataU p f ι X Φ) (i : ι)
    (hconj : ConjInvariant Φ) {t : StatedLieTag} {k e : ℕ} (ht : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t k p e) (he : e = f ∨ (t = .trialityD4 ∧ 3 * e = f))
    (hc : D.kind i = compModel p e t k) : Ih8Model p f Φ t k e where
  isFundTag := ht
  admissible := hadm
  exp_eq := he
  ψ := castHom hc (D.hom i)
  ker_le_center := castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)
  surj := by
    have h := lieSystemDataU_surjective_hom D i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  cls := {R | R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D ∧
    R.map (castHom hc (D.hom i)) ∈ Φ}
  cls_sub := fun _ hR => hR.1
  mem_iff := by
    intro L
    constructor
    · intro hL
      obtain ⟨j, R, hR, rfl⟩ := D.fundamental L hL
      obtain rfl : j = i := Subsingleton.elim j i
      obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom j) hR
      exact ⟨R', ⟨hR', by rw [hRR]; exact hL⟩, hRR.symm⟩
    · rintro ⟨R, hR, rfl⟩
      exact hR.2
  cls_conj := by
    intro R hR g
    refine ⟨Asc77.OmegaLie.fund_conj hR.1 g, ?_⟩
    have := map_conj_eq_conjSub_map (castHom hc (D.hom i)) g R
    change Subgroup.map (castHom hc (D.hom i)) (conjSub g R) ∈ Φ
    rw [show Subgroup.map (castHom hc (D.hom i)) (conjSub g R) =
      conjSub (castHom hc (D.hom i) g) (R.map (castHom hc (D.hom i))) from this]
    exact hconj _ _ hR.2

end Model

section Main


variable {Y₀ : Type} [Group Y₀] [Finite Y₀] {Λ₀ : Set (Subgroup Y₀)}

theorem sectionThm6U_aux {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card Y₀ < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    ∃ D : LieSystemDataU 3 1 (Fin 1)
        (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))
        (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))),
      (∃ (t : StatedLieTag) (k : ℕ), ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨
        (t = .G2 ∧ k = 0) ∨ (t = .trialityD4 ∧ k = 0)) ∧ CompIs 3 1 (D.kind 0) t k) ∨
        D.kind 0 = Q3.CompData.m11 := by
  obtain ⟨D⟩ := sectionThm6U_exists_system hIH hn hΩ hne hDE
  refine ⟨D, ?_⟩
  have hconj := conjInvariant_oddQuotientFamily
    (hypOmegaModU_restrict hΩ (omegaGen Λ₀)).conjInvariant
  have hno : ∀ A ∈ oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀)),
      ∀ B ∈ oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀)), ¬ Commutes A B :=
    fun A hA B hB h => false_of_commutes_in_section hΩ hDE hA hB h
  have hΦne := sectionFamily_nonempty hne
  rcases D.valid 0 with ⟨t, k, e, hft, hadm, he, hc⟩ | ⟨-, hc | hc⟩
  · left
    have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩ <;> omega
    subst he1
    let M : Ih8Model 3 1 (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) t k 1 :=
      ih8ModelOfSystemU D 0 hconj hft hadm (Or.inl rfl) hc
    refine ⟨t, k, ?_, ⟨1, Or.inl rfl, hft, hadm, hc⟩⟩
    by_cases hG2 : t = .G2
    · subst hG2
      obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    by_cases hD4 : t = .trialityD4
    · subst hD4
      have hk : k = 0 := hadm.2.2
      subst hk
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    by_cases hL3 : t = .PSL ∧ k = 3
    · exact Or.inl hL3
    by_cases hU3 : t = .PSU ∧ k = 3
    · exact Or.inr (Or.inl hU3)
    exfalso
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have h3' : ¬ ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) := by
      rintro (h | h)
      · exact hL3 h
      · exact hU3 h
    obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hΦne
    obtain ⟨R, hR, S, hS, hRS⟩ :=
      exists_commuting_fund (by norm_num : (3 : ℕ) ≠ 2) hft hadm hG2 hD4 hA1 h3' (M.cls_sub hR₀)
    have hK := M.map_mem (M.fund_subset_cls hΦne hG2 hD4 hR)
    have hJ := M.map_mem (M.fund_subset_cls hΦne hG2 hD4 hS)
    exact hno _ hK _ hJ (ih8_commutes_map M.ψ hRS)
  · exfalso
    exact hTop (top_mem_of_sl23 D 0 hc)
  · exact Or.inr hc

theorem sectionThm6U_datum {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card Y₀ < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    (∃ (t : StatedLieTag) (k e' : ℕ)
      (_ : Ih8Model 3 1 (oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) t k e'),
        (t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3) ∨ (t = .G2 ∧ k = 0) ∨
          (t = .trialityD4 ∧ k = 0)) ∨
      SectionCompU 3 1 Λ₀ (omegaGen Λ₀) Q3.CompData.m11 := by
  obtain ⟨D, h | h⟩ := sectionThm6U_aux hIH hn hΩ hne hDE hTop
  · left
    obtain ⟨t, k, htag, e, he, hft, hadm, hc⟩ := h
    have hconj := conjInvariant_oddQuotientFamily
      (hypOmegaModU_restrict hΩ (omegaGen Λ₀)).conjInvariant
    exact ⟨t, k, e, ih8ModelOfSystemU D 0 hconj hft hadm he hc, htag⟩
  · exact Or.inr ⟨D, h⟩

theorem sectionThm6U {n : ℕ} (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card Y₀ < n)
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    SectionLieTypeU 3 1 Λ₀ (omegaGen Λ₀) .PSL 3 ∨ SectionLieTypeU 3 1 Λ₀ (omegaGen Λ₀) .PSU 3 ∨
      SectionLieTypeU 3 1 Λ₀ (omegaGen Λ₀) .G2 0 ∨
        SectionLieTypeU 3 1 Λ₀ (omegaGen Λ₀) .trialityD4 0 ∨
          SectionCompU 3 1 Λ₀ (omegaGen Λ₀) Q3.CompData.m11 := by
  obtain ⟨D, h | h⟩ := sectionThm6U_aux hIH hn hΩ hne hDE hTop
  · obtain ⟨t, k, htag, hc⟩ := h
    rcases htag with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨D, hc⟩
    · exact Or.inr (Or.inl ⟨D, hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨D, hc⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨D, hc⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨D, h⟩)))

end Main

end CFSG.ClassicalInvolution.Q3.Q3T6
