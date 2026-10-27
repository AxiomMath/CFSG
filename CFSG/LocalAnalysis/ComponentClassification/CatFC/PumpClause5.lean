module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpEvenArm
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpL4Order
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpClause2
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
  (two_pow_twelve_dvd_card_lieModel_T not_alt_of_lieModel_psl_four card_psl_four)

variable {S : Type} [Group S] [Finite S]

theorem statedLieAdmissible_psl_four_two_pow (i : ℕ) : StatedLieAdmissible .PSL 4 2 (2 ^ i) :=
  ⟨Nat.prime_two, Nat.one_le_two_pow, by norm_num, fun h => by simp at h, fun h => by simp at h⟩

@[expose] def cardPSL4 (i : ℕ) : ℕ :=
  (2 ^ 2 ^ i) ^ 6 * (((2 ^ 2 ^ i) ^ 2 - 1) * (((2 ^ 2 ^ i) ^ 3 - 1) * ((2 ^ 2 ^ i) ^ 4 - 1)))

theorem pow_dvd_cardPSL4 (i : ℕ) : 2 ^ (6 * 2 ^ i) ∣ cardPSL4 i := by
  unfold cardPSL4
  rw [← pow_mul, mul_comm (2 ^ i) 6]
  exact Dvd.intro _ rfl

theorem rows_psl4 (s : TauCeti.SporadicName) {i : ℕ} (hi : 1 ≤ i)
    (hd : cardPSL4 i ∣ AGLEmbedding.sporOrd s) :
    ¬ SporadicInnerRow s (cardPSL4 i) ∧ ¬ SporadicOuterRow s (cardPSL4 i) := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | hi3
  · have h1 : cardPSL4 1 = 987033600 := by decide
    rw [h1] at hd ⊢
    cases s <;> first
      | exact absurd hd (by simp only [AGLEmbedding.sporOrd]; decide)
      | (simp only [SporadicInnerRow, SporadicOuterRow]; decide)
  · have h2 : cardPSL4 2 = 1148120010326016000 := by decide
    rw [h2] at hd ⊢
    cases s <;> first
      | exact absurd hd (by simp only [AGLEmbedding.sporOrd]; decide)
      | (simp only [SporadicInnerRow, SporadicOuterRow]; decide)
  · exfalso
    have h48 : 2 ^ 48 ∣ cardPSL4 i := by
      refine (Nat.pow_dvd_pow 2 ?_).trans (pow_dvd_cardPSL4 i)
      calc 48 = 6 * 2 ^ 3 := by norm_num
        _ ≤ 6 * 2 ^ i := Nat.mul_le_mul_left 6 (Nat.pow_le_pow_right (by norm_num) hi3)
    have h := h48.trans hd
    revert h
    cases s <;> simp only [AGLEmbedding.sporOrd] <;> decide

theorem lieModel_psl4_of_even_psl4 (hO : LieOrderFormulasInput)
    (hEI : ∀ (T : Type) [Group T], EvenLieType T → ∀ u : T, orderOf u = 2 →
      ∀ B : Subgroup ↥(centralizer ({u} : Set T)), ¬ IsComponent B)
    (hT : EvenOuterTypedInput) [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (heven : EvenLieType S) {σ : MulAut S} (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)}
    (hD : IsComponent D) {i : ℕ} (hi : 1 ≤ i) (hL : LieModel (↥D ⧸ center ↥D) .PSL 4 2 (2 ^ i)) :
    LieModel S .PSL 4 2 (2 ^ (i + 1)) := by
  obtain ⟨τ, n, f, hadm, hmod⟩ := heven
  obtain ⟨-, h⟩ := even_arm_typed hEI hT hna hadm hmod hσ hD
  have h12 := two_pow_twelve_dvd_card_lieModel_T hi hL
  rcases h with ⟨τ', n', f', hadm', hmod', himp⟩ | hA | hU
  · obtain ⟨h1, h2, h3⟩ := eq_psl_four_of_lieModel_two hO hadm' hmod' hi hL
    obtain ⟨rfl, rfl, rfl⟩ := himp h1 h2
    subst h3
    rw [pow_succ']
    exact hmod
  · exfalso
    obtain ⟨eA⟩ := hA
    rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h12
    revert h12
    decide
  · exfalso
    exact SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two hO hL
      (fun h => absurd h.2.1 (by norm_num)) (fun h => absurd h.2.1 (by norm_num))
      (fun h => absurd h.1 (by decide))
      ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num, ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩, hU⟩

theorem clause5_of_inputs (I : ArmInputs) (hT : EvenOuterTypedInput) [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcat : Catalog S) {σ : MulAut S} (hσ : orderOf σ = 2)
    {D : Subgroup ↥(fixedSubgroup σ)} (hD : IsComponent D) {i : ℕ} (hi : 1 ≤ i)
    (hL : LieModel (↥D ⧸ center ↥D) .PSL 4 2 (2 ^ i)) : LieModel S .PSL 4 2 (2 ^ (i + 1)) := by
  have h12 := two_pow_twelve_dvd_card_lieModel_T hi hL
  have hcard : Nat.card (↥D ⧸ center ↥D) = cardPSL4 i := card_psl_four Nat.one_le_two_pow hL
  rcases catalog_fixed_component I.gls I.evenInner I.evenOuter hna hcat hσ hD with
    ⟨n, k, -, hk5, -, -, -, hDk⟩ | ⟨-, hodd⟩ | ⟨heven, -⟩ | ⟨s', ⟨es⟩⟩
  · exfalso
    obtain ⟨e⟩ := hDk
    by_cases hk9 : 9 ≤ k
    · exact CFSG.OddStandard.AltStdSec.not_evenLieType_alt I.order hk9
        (evenLieType_transport e ⟨.PSL, 4, 2 ^ i, statedLieAdmissible_psl_four_two_pow i, hL⟩)
    · exact not_alt_of_lieModel_psl_four hi (by omega)
        (by interval_cases k <;> decide) hL ⟨e⟩
  · exfalso
    rcases hodd with hoddD | hL8
    · exact SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two I.order hL
        (fun h => absurd h.2.1 (by norm_num)) (fun h => absurd h.2.1 (by norm_num))
        (fun h => absurd h.1 (by decide)) hoddD
    · have hadmL : StatedLieAdmissible .PSL 2 2 3 :=
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩
      obtain ⟨-, h1, -⟩ := I.order _ .PSL 2 2 3 hadmL hL8
      have h504 : Nat.card ↥D = 504 := by
        simp only [lieOrderDivisor, lieOrderNumerator] at h1
        norm_num [Finset.Icc_self] at h1
        omega
      have hle : Nat.card (↥D ⧸ center ↥D) ≤ Nat.card ↥D :=
        Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
      have hpos : 0 < Nat.card (↥D ⧸ center ↥D) := Nat.card_pos
      have := Nat.le_of_dvd hpos h12
      omega
  · exact lieModel_psl4_of_even_psl4 I.order I.evenInner hT hna heven hσ hD hi hL
  · exfalso
    obtain ⟨hdvd, hin, hout⟩ := I.table ‹IsSimpleGroup S› hna es hσ hD
    rw [hcard] at hdvd hin hout
    obtain ⟨hr1, hr2⟩ := rows_psl4 s' hi hdvd
    by_cases hinn : σ ∈ (MulAut.conj : S →* MulAut S).range
    · exact hr1 (hin hinn)
    · exact hr2 (hout hinn)

end CFSG.ComponentClassification.CatFC
