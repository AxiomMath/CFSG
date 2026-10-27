module

public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec
public import CFSG.ClassicalInvolution.AschTight.S19BStmt
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Goldschmidt

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_centralizer_of_stronglyClosed (hB1 : S19B.GoldschmidtB1Tmp) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G) {B : Subgroup G}
    (hBS : B ≤ (S : Subgroup G)) (hB : B ≠ ⊥) (hsc : fusionStronglyClosed (B : Set G) S) :
    Group.IsSolvable ↥(Subgroup.centralizer (B : Set G)) := by
  have h1 := hB1 G hnonab S B hBS hB hsc
  rw [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mp h1

end Goldschmidt

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
  have : Nontrivial Q := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact not_subsingleton (Q ⧸ Subgroup.center Q) inferInstance
  have : Group.IsPerfect Q := ⟨hQ.1⟩
  exact Group.IsPerfect.not_isSolvable Q


section Nonsolvable


variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem not_isSolvable_of_system (hM : Q3.M11Facts) [Subsingleton ι]
    (D : LieSystemDataU 3 1 ι X Φ) (i : ι) (hTop : (⊤ : Subgroup X) ∉ Φ)
    (hΦ : Φ.Nonempty) : ¬ Group.IsSolvable X := by
  intro hsol
  obtain ⟨L, hL⟩ := hΦ
  have hψ1 : ∃ x, D.hom i x ≠ 1 := by
    have h24 := D.card_eq rfl L hL
    have : ∃ y ∈ L, y ≠ 1 := by
      by_contra h
      push Not at h
      have : L = ⊥ := (Subgroup.eq_bot_iff_forall L).mpr h
      rw [this, Subgroup.card_bot] at h24
      omega
    obtain ⟨y, -, hy⟩ := this
    obtain ⟨x, rfl⟩ := lieSystemDataU_surjective_hom D i y
    exact ⟨x, hy⟩
  have hsolr : Group.IsSolvable ↥(D.hom i).range := inferInstance
  rcases D.valid i with ⟨t, n, e, hft, hadm, he, hc⟩ | ⟨-, hc | hc⟩
  · have he1 : e = 1 := by
      rcases he with he | ⟨-, he⟩ <;> omega
    subst he1
    exact not_isSolvable_of_isQuasisimple
      (Q3.range_model3 ModelFacts.modelClauseZero hft hadm hc (D.hom i) (D.ker_le_center i)
        hψ1).1 hsolr
  · exact hTop (top_mem_of_sl23 D i hc)
  · exact not_isSolvable_of_isQuasisimple (Q3.range_m11 hM hc (D.hom i) hψ1).1 hsolr

end Nonsolvable

section EndGame


variable {Y₀ : Type} [Group Y₀] [Finite Y₀] {Λ₀ : Set (Subgroup Y₀)}

theorem not_isSolvable_section {n : ℕ} (hM : Q3.M11Facts) (hIH : CITBelowT (.sl2 3 1) n)
    (hn : Nat.card Y₀ < n) (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty)
    (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    ¬ Group.IsSolvable (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀)) := by
  obtain ⟨D⟩ := sectionThm6U_exists_system hIH hn hΩ hne hDE
  exact not_isSolvable_of_system hM D 0 hTop (sectionFamily_nonempty hne)

theorem not_isSolvable_of_section {n : ℕ} (hM : Q3.M11Facts) (hIH : CITBelowT (.sl2 3 1) n)
    (hn : Nat.card Y₀ < n) (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty)
    (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) :
    ¬ Group.IsSolvable Y₀ := by
  intro hsol
  apply not_isSolvable_section hM hIH hn hΩ hne hDE hTop
  have : Group.IsSolvable ↥(omegaGen Λ₀) := inferInstance
  exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)

theorem false_of_stronglyClosed_three {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hB1 : S19B.GoldschmidtB1Tmp) (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {B : Subgroup G} (hBS : B ≤ (S : Subgroup G)) (hB : B ≠ ⊥)
    (hsc : fusionStronglyClosed (B : Set G) S) {n : ℕ} (hM : Q3.M11Facts)
    (hIH : CITBelowT (.sl2 3 1) n) (hn : Nat.card ↥(Subgroup.centralizer (B : Set G)) < n)
    {Λ₀ : Set (Subgroup ↥(Subgroup.centralizer (B : Set G)))}
    (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hne : Λ₀.Nonempty) (hDE : DEdgeless Λ₀)
    (hTop : (⊤ : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))) ∉
      oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) : False :=
  not_isSolvable_of_section hM hIH hn hΩ hne hDE hTop
    (isSolvable_centralizer_of_stronglyClosed hB1 hnonab S hBS hB hsc)

end EndGame

end CFSG.ClassicalInvolution.Q3.Q3T6
