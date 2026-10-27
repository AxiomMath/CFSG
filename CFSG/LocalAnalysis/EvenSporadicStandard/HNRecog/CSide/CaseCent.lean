module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.SetupModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictExtra
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.FreeSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.LinkCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.GrpShapeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictExtraPlane

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog.Fpf
  CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem CSideSetup.cent_eq_of_one_coord [Finite C]
    (hC : WeakHyp C Q) (S : CSideSetup C Q) {p : ℕ} (hp : p = 3 ∨ p = 5) {σ : C}
    (hσL : σ ∈ commutator C) (hσ : orderOf σ = p) (hg : orderOf (S.θ ⟨σ, hσL⟩) = p)
    (h1 : (S.θ ⟨σ, hσL⟩).1 = 1 ∨ (S.θ ⟨σ, hσL⟩).2 = 1) :
    Q ⊓ Subgroup.centralizer ({σ} : Set C) = centerOf Q := by
  haveI : Finite Q := hC.finite_Q
  have hE := hC.isExtraspecialPGroup
  have hρ : Odd (orderOf σ) := by
    rw [hσ]
    rcases hp with rfl | rfl <;> norm_num
  have hM := S.model hC
  have hord : orderOf (S.θ ⟨σ, hσL⟩) = 3 ∨ orderOf (S.θ ⟨σ, hσL⟩) = 5 := by
    rcases hp with rfl | rfl
    · exact Or.inl hg
    · exact Or.inr hg
  refine (cSide_cent_eq_centerOf_iff hE (ρ := σ) hρ).mpr ?_
  intro v hv
  rw [S.rho_eq hσL] at hv
  exact hM.fixed_zero (S.θ ⟨σ, hσL⟩) hord h1 v hv

theorem CSideSetup.cent_plusExtraspecial_of_three [Finite C]
    (hC : WeakHyp C Q) (S : CSideSetup C Q) {σ : C} (hσL : σ ∈ commutator C)
    (hσ : orderOf σ = 3) (hg : orderOf (S.θ ⟨σ, hσL⟩) = 3) (h1 : (S.θ ⟨σ, hσL⟩).1 ≠ 1)
    (h2 : (S.θ ⟨σ, hσL⟩).2 ≠ 1) :
    IsPlusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({σ} : Set C)) := by
  haveI : Finite Q := hC.finite_Q
  have hE := hC.isExtraspecialPGroup
  have hρ : Odd (orderOf σ) := by rw [hσ]; norm_num
  have hM := S.model hC
  obtain ⟨hfix, hnd, hplane⟩ := hM.three_both (S.θ ⟨σ, hσL⟩) hg h1 h2
  rw [← S.rho_eq hσL] at hfix hnd hplane
  obtain ⟨hext, hcard⟩ := cSide_cent_isExtraspecial hE (ρ := σ) hρ hfix hnd
  obtain ⟨E, hEsub, hEab, hEcard⟩ := cSide_cent_elemAbelian_of_plane hE (ρ := σ) hρ hplane
  unfold IsPlusExtraspecial
  exact ⟨hext, by rw [hcard], E, hEsub, hEab, by rw [hEcard]⟩

theorem CSideSetup.cent_of_five_both [Finite C]
    (hC : WeakHyp C Q) (S : CSideSetup C Q) {t : C} (ht : t ∉ commutator C)
    (ht2 : (t : C ⧸ Q) ^ 2 = 1)
    (hcard : Nat.card {q : C // q ∈ Q ∧ ⁅q, t⁆ ∈ centerOf Q} ≤ 2 ^ 5) {σ : C}
    (hσL : σ ∈ commutator C) (hσ : orderOf σ = 5) (hg : orderOf (S.θ ⟨σ, hσL⟩) = 5)
    (h1 : (S.θ ⟨σ, hσL⟩).1 ≠ 1) (h2 : (S.θ ⟨σ, hσL⟩).2 ≠ 1) :
    (IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2 →
      Q ⊓ Subgroup.centralizer ({σ} : Set C) = centerOf Q) ∧
    (¬ IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2 →
      IsMinusExtraspecial 2 (Q ⊓ Subgroup.centralizer ({σ} : Set C))) := by
  haveI : Finite Q := hC.finite_Q
  have hE := hC.isExtraspecialPGroup
  have hρ : Odd (orderOf σ) := by rw [hσ]; norm_num
  have hM := S.model hC
  have hfree : cSideFreeSwap (extraspecialQuadForm hE) S.σ (conjLinEquiv hQn t) :=
    CSideSetup.cSideFreeSwap_of_card_le hC S ht ht2 hcard
  have hAiff : (∃ l : A5 × A5, S.σ l * conjLinEquiv hQn t * S.σ (S.θ ⟨σ, hσL⟩) =
        S.σ (S.θ ⟨σ, hσL⟩) * (S.σ l * conjLinEquiv hQn t)) ↔
      IsConj (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2 :=
    (cSide_swapCent_iff hC S ht hσL).trans
      (cSide_exists_outer_cent_iff (S.θ ⟨σ, hσL⟩).1 (S.θ ⟨σ, hσL⟩).2)
  obtain ⟨hfive_fwd, hfive_bwd⟩ :=
    hM.five_both (conjLinEquiv hQn t) hfree (S.θ ⟨σ, hσL⟩) hg h1 h2
  constructor
  · intro hconj
    refine (cSide_cent_eq_centerOf_iff hE (ρ := σ) hρ).mpr ?_
    intro v hv
    rw [S.rho_eq hσL] at hv
    exact hfive_fwd (hAiff.mpr hconj) v hv
  · intro hnc
    obtain ⟨hcard16, hnd, hnplane⟩ := hfive_bwd (fun hA => hnc (hAiff.mp hA))
    have hfix : Nat.card {v : Additive (Abelianization Q) // conjLinEquiv hQn σ v = v} = 16 := by
      rw [S.rho_eq hσL]
      exact hcard16
    have hnd' : cSideFixedNondeg (extraspecialQuadForm hE) (conjLinEquiv hQn σ) := by
      rwa [S.rho_eq hσL]
    have hnplane' : ¬ cSideFixedPlane (extraspecialQuadForm hE) (conjLinEquiv hQn σ) := by
      rwa [S.rho_eq hσL]
    obtain ⟨hext, hcard5⟩ := cSide_cent_isExtraspecial hE (ρ := σ) hρ hfix hnd'
    unfold IsMinusExtraspecial
    refine ⟨hext, ?_, ?_⟩
    · rw [hcard5]
    · rintro ⟨E, hEle, hEa, hEc⟩
      exact hnplane' (cSide_plane_of_cent_elemAbelian hE hEle hEa hEc)

end CFSG.EvenSporadicStandard.HNRecog.CSide
