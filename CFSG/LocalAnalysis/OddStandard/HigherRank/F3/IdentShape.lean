module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.IdentTable
public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Lift
public import CFSG.LocalAnalysis.ComponentClassification.TBLitSwap

public section

namespace CFSG.OddStandard.HigherRank.F3.Ident

open Subgroup CFSG CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.HarrisLit

theorem isMTypeSchur_clauses {J : Type} [Group J] [Finite J] (hJ2 : IsTwoQuasisimple J)
    {p : ℕ} (hM : IsMTypeSchur p J) :
    IsSimpleChevalleyOver p (J ⧸ fusionZStar J) ∧ Even (Nat.card ↥(fusionZStar J)) ∧
      ∀ n r : ℕ, 0 < n → 0 < r →
        (Blueprint.LieModel (J ⧸ fusionZStar J) .PSL (2 * n) p r ∨
          Blueprint.LieModel (J ⧸ fusionZStar J) .PSU (2 * n) p r) →
        ordProj[2] (Nat.card ↥(fusionZStar J)) =
          ordProj[2] (Nat.card (griessHopfMultiplier (J ⧸ fusionZStar J))) := by
  rcases hM with ⟨-, hc, hev, hcl⟩ | ⟨_, ⟨e⟩⟩
  · exact ⟨hc, hev, hcl⟩
  · exfalso
    haveI : Group.IsPerfect (J ⧸ pPrimeCore 2 J) := hJ2.2.1
    exact ComponentClassification.TBLit.not_isPerfect_sl2Three
      (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)

theorem not_partialCentre_of_psl_psu {J : Type} [Group J] [Finite J] (hJ2 : IsTwoQuasisimple J)
    (hM : IsMTypeSchur 3 J) {τ : StatedLieTag} {n : ℕ}
    (hm : Blueprint.LieModel (J ⧸ fusionZStar J) τ n 3 1)
    (hτ : (τ = .PSL ∨ τ = .PSU) ∧ (n = 4 ∨ n = 6)) : ¬ PartialCentre J := by
  obtain ⟨-, -, hc⟩ := isMTypeSchur_clauses hJ2 hM
  intro hP
  unfold PartialCentre at hP
  rcases hτ with ⟨hτ, hn⟩
  rcases hτ with rfl | rfl
  · rcases hn with rfl | rfl
    · have h := hc 2 1 (by norm_num) (by norm_num) (Or.inl hm)
      rw [h] at hP
      exact (lt_irrefl _) hP
    · have h := hc 3 1 (by norm_num) (by norm_num) (Or.inl hm)
      rw [h] at hP
      exact (lt_irrefl _) hP
  · rcases hn with rfl | rfl
    · have h := hc 2 1 (by norm_num) (by norm_num) (Or.inr hm)
      rw [h] at hP
      exact (lt_irrefl _) hP
    · have h := hc 3 1 (by norm_num) (by norm_num) (Or.inr hm)
      rw [h] at hP
      exact (lt_irrefl _) hP

theorem shape_cover_input (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hE7 : E7ThreeRow) {J : Type} [Group J] [Finite J] (hJ2 : IsTwoQuasisimple J)
    (hM : IsMTypeSchur 3 J) (hs : ClassBShape J) :
    ¬ PartialCentre (J ⧸ pPrimeCore 2 J) ∨
      ∀ m : griessHopfMultiplier ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)),
        m ^ 2 = 1 := by
  obtain ⟨τ, n, hm, hs'⟩ := hs
  obtain ⟨e⟩ := L35.nonempty_fusionZStar_quotient_equiv J
  have hm' : Blueprint.LieModel ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J))
      τ n 3 1 := ComponentClassification.GSThmB.OddQuot.lieModel_of_equiv e hm
  have hker : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 J)).ker :=
    ComponentClassification.GSThmB.OddQuot.not_two_dvd_card_ker (H := J)
  rcases hs' with hPSL | hPSU | hPSp | hPOm | hE7shape
  · obtain ⟨hτ, hn⟩ := hPSL
    left
    have hnot : ¬ PartialCentre J :=
      not_partialCentre_of_psl_psu hJ2 hM hm ⟨Or.inl hτ, hn⟩
    have hiff := partialCentre_iff_of_surjective_odd
      (QuotientGroup.mk' (pPrimeCore 2 J)) (QuotientGroup.mk'_surjective _) hker
    intro hQ
    exact hnot (hiff.mpr hQ)
  · obtain ⟨hτ, hn⟩ := hPSU
    left
    have hnot : ¬ PartialCentre J :=
      not_partialCentre_of_psl_psu hJ2 hM hm ⟨Or.inr hτ, hn⟩
    have hiff := partialCentre_iff_of_surjective_odd
      (QuotientGroup.mk' (pPrimeCore 2 J)) (QuotientGroup.mk'_surjective _) hker
    intro hQ
    exact hnot (hiff.mpr hQ)
  · obtain ⟨hτ, hn⟩ := hPSp
    right
    exact sq_eq_one_of_shape hGA hE7 hm' (Or.inl ⟨hτ, hn⟩)
  · obtain ⟨hτ, hn⟩ := hPOm
    right
    exact sq_eq_one_of_shape hGA hE7 hm' (Or.inr (Or.inl ⟨hτ, hn⟩))
  · right
    exact sq_eq_one_of_shape hGA hE7 hm' (Or.inr (Or.inr hE7shape))

end CFSG.OddStandard.HigherRank.F3.Ident
