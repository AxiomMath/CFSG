module

public import CFSG.Foundations.Basic
import CFSG.Foundations.HigherElementaryThompson
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG Subgroup

private theorem card_eq_two_pow_pRank_of_isElementaryAbelian {Y : Type} [Group Y] [Finite Y]
    {B : Subgroup Y}
    (hB : CFSG.IsElementaryAbelian 2 ↥B) : Nat.card ↥B = 2 ^ pRank 2 ↥B := by
  obtain ⟨n, hn⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥B).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hn]
  exact hn

private theorem le_iSup_inf_centralizer_of_card {Y : Type} [Group Y] [Finite Y] {D W : Subgroup Y}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hr : 1 ≤ pRank 2 ↥D) (hW : Odd (Nat.card ↥W))
    (hDW : D ≤ normalizer (W : Set Y)) :
    W ≤ ⨆ S ∈ CFSG.Open.signalizerFunctorEk 2 (pRank 2 ↥D - 1) D, W ⊓ centralizer (S : Set Y) := by
  have hlarge : 2 ^ (pRank 2 ↥D - 1 + 1) ≤ Nat.card ↥D := by
    rw [card_eq_two_pow_pRank_of_isElementaryAbelian hD]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact (CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2
    (pRank 2 ↥D - 1) Nat.prime_two D W
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 D).mp hD) hlarge hDW
    (Nat.coprime_two_left.mpr hW)).ge

private theorem isElementaryAbelian_of_le_aux {Y : Type} [Group Y] {A B : Subgroup Y}
    (hA : CFSG.IsElementaryAbelian 2 ↥A) (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B :=
  CFSG.IsElementaryAbelian.of_le hA hBA

theorem lemma_III2_910 {Y : Type} [Group Y] [Finite Y] {D W : Subgroup Y}
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (hr : 2 ≤ pRank 2 ↥D) (hW : Odd (Nat.card ↥W))
    (hDW : D ≤ normalizer (W : Set Y))
    (hgam : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set Y) ≤ normalizer (W : Set Y)) :
    ∀ w ∈ W, ∀ u ∈ pCore 2 Y, w * u = u * w := by
  have hPn : (pCore 2 Y).Normal := pCore_normal
  have hP2 : IsPGroup 2 ↥(pCore 2 Y) := pCore_isPGroup
  have hPW : Nat.Coprime (Nat.card ↥(pCore 2 Y)) (Nat.card ↥W) := by
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hW)
  have hPWbot : pCore 2 Y ⊓ W = ⊥ := disjoint_iff.mp (disjoint_of_coprime_natCard hPW)
  have hnormP : normalizer ((pCore 2 Y : Subgroup Y) : Set Y) = ⊤ := normalizer_eq_top_iff.mpr hPn
  have key : ∀ S ∈ CFSG.Open.signalizerFunctorEk 2 (pRank 2 ↥D - 1) D,
      W ⊓ centralizer (S : Set Y) ≤ centralizer ((pCore 2 Y : Subgroup Y) : Set Y) := by
    rintro S ⟨hSD, hScard⟩
    have hSea : CFSG.IsElementaryAbelian 2 ↥S := isElementaryAbelian_of_le_aux hD hSD
    have hSrank : pRank 2 ↥D - 1 ≤ pRank 2 ↥S := (CFSG.pRank_eq_of_card_eq_pow one_lt_two hScard).ge
    have hCW : centralizer (S : Set Y) ≤ normalizer (W : Set Y) := hgam S hSD hSrank
    refine CFSG.RankThreeCoreUniqueness.Helpers.ambient_subgroup_axb_centralizer_le 2 Nat.prime_two
      S (W ⊓ centralizer (S : Set Y)) (pCore 2 Y) (CFSG.IsElementaryAbelian.isPGroup 2 ↥S) hP2
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left) hPW)
      (by rw [hnormP]; exact le_top) (by rw [hnormP]; exact le_top) inf_le_right ?_
    intro a ha
    rw [mem_centralizer_iff]
    intro q hq
    obtain ⟨haW, -⟩ := mem_inf.mp ha
    obtain ⟨hqP, hqC⟩ := mem_inf.mp hq
    have h1 : q * a * q⁻¹ * a⁻¹ ∈ W := by
      have hqa : q * a * q⁻¹ ∈ W := (mem_normalizer_iff.mp (hCW hqC) a).mp haW
      exact W.mul_mem hqa (W.inv_mem haW)
    have h2 : q * a * q⁻¹ * a⁻¹ ∈ pCore 2 Y := by
      have : q * a * q⁻¹ * a⁻¹ = q * (a * q⁻¹ * a⁻¹) := by group
      rw [this]
      exact (pCore 2 Y).mul_mem hqP (hPn.conj_mem q⁻¹ ((pCore 2 Y).inv_mem hqP) a)
    have h3 : q * a * q⁻¹ * a⁻¹ = 1 := mem_bot.mp (hPWbot ▸ mem_inf.mpr ⟨h2, h1⟩)
    calc q * a = (q * a * q⁻¹ * a⁻¹) * (a * q) := by group
      _ = a * q := by rw [h3, one_mul]
  intro w hw u hu
  have hWP : W ≤ centralizer ((pCore 2 Y : Subgroup Y) : Set Y) :=
    (le_iSup_inf_centralizer_of_card hD (by omega) hW hDW).trans (iSup₂_le key)
  exact (mem_centralizer_iff.mp (hWP hw) u hu).symm

theorem exists_component_not_centralized {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {D W : Subgroup Y} (hD : CFSG.IsElementaryAbelian 2 ↥D) (hr : 2 ≤ pRank 2 ↥D) (hW : Odd (Nat.card ↥W))
    (hW1 : W ≠ ⊥) (hDW : D ≤ normalizer (W : Set Y))
    (hgam : ∀ E : Subgroup Y, E ≤ D → pRank 2 ↥D - 1 ≤ pRank 2 ↥E →
      centralizer (E : Set Y) ≤ normalizer (W : Set Y)) :
    ∃ J : Subgroup Y, IsComponent J ∧ ¬ W ≤ centralizer (J : Set Y) := by
  by_contra hcon
  have hcomp : ∀ J : Subgroup Y, IsComponent J → W ≤ centralizer (J : Set Y) := fun J hJ =>
    not_not.mp fun h => hcon ⟨J, hJ, h⟩
  have hLay : layer Y ≤ centralizer (W : Set Y) :=
    sSup_le fun J hJ => le_centralizer_iff.mp (hcomp J hJ)
  have hP : pCore 2 Y ≤ centralizer (W : Set Y) := fun u hu =>
    mem_centralizer_iff.mpr fun w hw => lemma_III2_910 hD hr hW hDW hgam w hw u hu
  have hFit : fittingSubgroup Y = pCore 2 Y := Fitting_eq_pcore Y 2 hO
  have hFstar : generalizedFitting Y ≤ centralizer (W : Set Y) :=
    sup_le (hFit ▸ hP) hLay
  have hWF : W ≤ centralizer (generalizedFitting Y : Set Y) := le_centralizer_iff.mpr hFstar
  have hcent := ComponentClassification.GeneralizedFitting.centralizer_le_fitting Y
  rw [← generalizedFitting_eq_componentClassification] at hcent
  have hWP : W ≤ pCore 2 Y := hFit ▸ (hWF.trans hcent)
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
  have hdvd : Nat.card ↥W ∣ 2 ^ n := hn ▸ card_dvd_of_le hWP
  have hcop : Nat.Coprime (Nat.card ↥W) (2 ^ n) :=
    Nat.Coprime.pow_right n (Nat.coprime_two_left.mpr hW).symm
  exact hW1 (W.eq_bot_of_card_eq (hcop.eq_one_of_dvd hdvd))

end CFSG.GH74.Generic.BProg.B2
