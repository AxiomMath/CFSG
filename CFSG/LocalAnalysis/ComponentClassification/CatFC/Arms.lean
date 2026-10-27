module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporNum
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.HarrisLit.T1.SporRow (not_oddLieOrder_sporOrder)
open CFSG.ComponentClassification.GSThmB.QPUSpor (sporOrder sporFactors)

variable {S : Type} [Group S] [Finite S]

theorem false_of_oddLie_fixedComponent (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) (hodd : OddLieType S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) {s : TauCeti.SporadicName}
    (hc : Nat.card (↥D ⧸ center ↥D) = sporOrder s) : False := by
  obtain ⟨τ, n, p, f, hp, hp2, hadm, hmod⟩ := hodd
  rcases hGLS S τ n p f hp hp2 hadm hmod σ hσ D hD with
    ⟨τ', n', f', hadm', hmod'⟩ | ⟨-, -, -, hL⟩
  · obtain ⟨-, h1, h2⟩ := hO _ τ' n' p f' hadm' hmod'
    rw [hc] at h1 h2
    exact not_oddLieOrder_sporOrder s ⟨τ', n', p, f', hp, hp2, hadm', h1, h2⟩
  · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
    obtain ⟨-, h1, -⟩ := hO _ .PSL 2 2 3 hadmL hL
    have h504 : Nat.card ↥D = 504 := by
      simp only [lieOrderDivisor, lieOrderNumerator] at h1
      norm_num [Finset.Icc_self] at h1
      omega
    have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    rw [hc, h504] at hle
    revert hle
    cases s <;> norm_num [sporOrder, sporFactors]

theorem false_of_evenLie_fixedComponent
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hEO : EvenLieOuterTwoComponentsInput) (hO : LieOrderFormulasInput)
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (heven : EvenLieType S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D)
    {s : TauCeti.SporadicName} (hc : Nat.card (↥D ⧸ center ↥D) = sporOrder s)
    (hne2 : ∀ {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}, StatedLieAdmissible t n 2 f →
      LieModel X t n 2 f → Nat.card X ≠ sporOrder s) : False := by
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨u, hu⟩ := hin
    have hκ := mulAut_conj_injective_of_simple hna
    have hu2 : orderOf u = 2 := by
      rw [← orderOf_injective _ hκ u, hu]
      exact hσ
    have hfix : fixedSubgroup σ = centralizer ({u} : Set S) := by
      rw [← hu]
      ext x
      rw [mem_centralizer_singleton_iff]
      change u * x * u⁻¹ = x ↔ x * u = u * x
      rw [mul_inv_eq_iff_eq_mul]
      exact eq_comm
    let φ := MulEquiv.subgroupCongr hfix
    exact hEI S heven u hu2 (D.map φ.toMonoidHom) (CFSG.LocalCores.isComponent_map_mulEquiv φ hD)
  · have hP : IsPComponent 2 D :=
      CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
    have hZD : Open.fusionZStar ↥D = center ↥D :=
      fusionZStar_eq_center_of_quasisimple hD.1 (pPrimeCore_ne_top_of_isPComponent hP)
    let e : ↥D ⧸ Open.fusionZStar ↥D ≃* ↥D ⧸ center ↥D := QuotientGroup.quotientMulEquivOfEq hZD
    obtain ⟨τ, n, f, hadm, hmod⟩ := heven
    rcases hEO S τ n f hadm hmod σ hσ hin D hP with
      ⟨τ', n', f', hadm', hmod'⟩ | hA | hU
    · exact hne2 hadm' (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hmod') hc
    · obtain ⟨eA⟩ := hA
      have h360 : Nat.card (↥D ⧸ center ↥D) = 360 := by
        rw [Nat.card_congr (e.symm.trans eA).toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      rw [hc] at h360
      revert h360
      cases s <;> norm_num [sporOrder, sporFactors]
    · have hadm3 : StatedLieAdmissible .PSU 3 3 1 :=
        ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      obtain ⟨-, h1, h2⟩ :=
        hO _ .PSU 3 3 1 hadm3 (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hU)
      rw [hc] at h1 h2
      exact not_oddLieOrder_sporOrder s ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, hadm3, h1, h2⟩

end CFSG.ComponentClassification.CatFC
