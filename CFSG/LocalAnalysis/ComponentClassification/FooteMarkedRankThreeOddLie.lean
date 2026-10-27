module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.Foundations.Basic
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClSp

public section

namespace CFSG.ComponentClassification.FooteMarked

open CFSG Subgroup

variable {B : Type} [Group B] [Finite B]

private theorem standardComponentOddCore_eq_pPrimeCore (H : Type*) [Group H] :
    Open.standardComponentOddCore H = CFSG.pPrimeCore 2 H := by
  unfold Open.standardComponentOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem normal_or_alternating_of_standard
    (hAS : ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X),
      Open.standardComponentIsStandard A → Open.standardComponentOddCore X = ⊥ →
      2 ≤ Open.pRank 2 (centralizer (A : Set X)) →
      RankTwoStandard.RankTwoOddLieType (RankTwoStandard.rankTwoQuot A) → A.Normal)
    (hO : pPrimeCore 2 B = ⊥) {A : Subgroup B} (hstd : Open.standardComponentIsStandard A)
    (hC : 2 ≤ CFSG.pRank 2 ↥(centralizer (A : Set B))) {T : Type} [Group T]
    (e : ↥A ⧸ center ↥A ≃* T)
    (hT : Nonempty (T ≃* alternatingGroup (Fin 7)) ∨ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      5 ≤ p ^ f ∧ Blueprint.LieModel T .PSL 2 p f) :
    A.Normal ∨ ∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) := by
  classical
  let Q := RankTwoStandard.rankTwoQuot A
  have hQsimple : IsSimpleGroup Q := hstd.1.2
  haveI : Finite Q :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center ↥A))
      (QuotientGroup.mk'_surjective (Subgroup.center ↥A))
  rcases hT with h7 | ⟨p, f, hp, hp2, hf, hq5, hmodelT⟩
  · obtain ⟨e7⟩ := h7
    exact Or.inr ⟨7, by norm_num, by norm_num, ⟨e.trans e7⟩⟩
  · have hmodelQ : Blueprint.LieModel Q .PSL 2 p f :=
      Blueprint.LieModel.of_mulEquiv e.symm hmodelT
    have hcard : Nat.card Q * 2 = p ^ f * ((p ^ f) ^ 2 - 1) :=
      GSThmB.QPUCl.card_mul_two_of_lieModel_psl_two hp hp2 hmodelQ
    set q := p ^ f with hq
    by_cases h5 : q = 5
    ·
      have h60 : Nat.card Q = 60 := by
        rw [h5] at hcard
        norm_num at hcard
        omega
      exact Or.inr ⟨5, by norm_num, by norm_num,
        CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60⟩
    · by_cases h9 : q = 9
      ·
        have hq9 : p ^ f = 9 := by
          rw [← hq]
          exact h9
        have hp3 : p = 3 := by
          have hdvd : p ∣ 3 ^ 2 := by
            have h := dvd_pow_self p (by omega : f ≠ 0)
            rw [hq9] at h
            exact h
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp (hp.dvd_of_dvd_pow hdvd) with
            h | h
          · exact absurd h hp.ne_one
          · exact h
        have hf2 : f = 2 := by
          rw [hp3] at hq9
          have hf3 : f ≤ 2 := by
            by_contra h
            have h3 : 3 ≤ f := by omega
            have hle : 3 ^ 3 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h3
            rw [hq9] at hle
            norm_num at hle
          interval_cases f
          · norm_num at hq9
          · rfl
        rw [hp3, hf2] at hmodelQ
        exact Or.inr ⟨6, by norm_num, by norm_num,
          Blueprint.LieModel.nonempty_mulEquiv_alternating_six hmodelQ⟩
      ·
        have hlie : Blueprint.OddLieType Q :=
          ⟨.PSL, 2, p, f, hp, hp2, hmodelQ.admissible, hmodelQ⟩
        have hnot5 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
          rintro ⟨e5⟩
          have h5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
            rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
            norm_num
          have hQcard : Nat.card Q = 60 := by
            rw [← h5card]
            exact Nat.card_congr e5.toEquiv
          have heq : p ^ f * ((p ^ f) ^ 2 - 1) = 5 * (5 ^ 2 - 1) := by
            rw [← hcard, hQcard]
            norm_num
          have hqeq : q = 5 := by
            rw [hq]
            exact GSThmB.QPUCl.eq_of_mul_sq_sub_one_eq (by omega) (by norm_num) heq
          exact h5 hqeq
        have hnot6 : ¬ Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
          rintro ⟨e6⟩
          have h6card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
            rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
            norm_num
          have hQcard : Nat.card Q = 360 := by
            rw [← h6card]
            exact Nat.card_congr e6.toEquiv
          have heq : p ^ f * ((p ^ f) ^ 2 - 1) = 9 * (9 ^ 2 - 1) := by
            rw [← hcard, hQcard]
            norm_num
          have hqeq : q = 9 := by
            rw [hq]
            exact GSThmB.QPUCl.eq_of_mul_sq_sub_one_eq (by omega) (by norm_num) heq
          exact h9 hqeq
        have hnot8 : ¬ CFSG.Open.StatedClassicalModel Q .PSL 2 2 3 := by
          intro h8
          have h504 : Nat.card Q = 504 :=
            CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_eight h8
          have h1008 : q * (q ^ 2 - 1) = 1008 := by
            have h := hcard
            rw [h504] at h
            omega
          have hqle : q ≤ 10 := by
            by_contra h
            have h11 : 11 ≤ q := by omega
            have hmono : 11 * (11 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
              Nat.mul_le_mul h11 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h11 2) 1)
            rw [h1008] at hmono
            norm_num at hmono
          interval_cases q <;> norm_num at h1008
        have hO' : Open.standardComponentOddCore B = ⊥ := by
          rw [standardComponentOddCore_eq_pPrimeCore, hO]
        have hC' : 2 ≤ Open.pRank 2 (centralizer (A : Set B)) := by
          rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
            ← CFSG.SectionRank.pRank_eq_open_pRank_top]
          exact hC
        exact Or.inl (hAS B A hstd hO' hC' ⟨hlie, hnot5, hnot6, hnot8⟩)

end CFSG.ComponentClassification.FooteMarked
