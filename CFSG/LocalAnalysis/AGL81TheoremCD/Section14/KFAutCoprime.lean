module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut

theorem exists_commute_of_card_eq_nine {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp3 : p ≠ 3) {R T : Subgroup X} (hRexp : ∀ x ∈ R, x ^ 3 = 1) (hR9 : Nat.card R = 9)
    (hT : IsPGroup p T) (hT1 : T ≠ ⊥) (hRT : R ≤ Subgroup.normalizer (T : Set X)) :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ x ∈ T, x ≠ 1 ∧ x * r = r * x := by
  have hpower : ∀ member : R, member ^ 3 = 1 := fun r =>
    Subtype.ext (by simpa using hRexp (r : X) r.2)
  have hcard : Nat.card R = 3 ^ 2 := by simpa using hR9
  have hcomp : ¬ 3 ∣ Nat.card T := by
    obtain ⟨n, hn⟩ := hT.exists_card_eq
    rintro ⟨k, hk⟩
    rw [hn] at hk
    exact hp3 (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Fact.out ⟨k, hk⟩).symm
  have hgen :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
      (G := X) 3 Nat.prime_three R T hpower hcard hcomp hRT
  have hjoin : (⨆ (r : R) (_ : r ≠ 1),
      T ⊓ Subgroup.centralizer ({(r : X)} : Set X)) ≠ ⊥ := by
    rw [← hgen]
    exact hT1
  obtain ⟨r, hr1, hne⟩ : ∃ r : R, r ≠ 1 ∧
      T ⊓ Subgroup.centralizer ({(r : X)} : Set X) ≠ ⊥ := by
    by_contra h
    exact hjoin (by
      rw [iSup_eq_bot]
      intro r
      rw [iSup_eq_bot]
      intro hr
      by_contra hbot
      exact h ⟨r, hr, hbot⟩)
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨r, r.2, fun h => hr1 (Subtype.ext h), x, x.2.1,
    fun h => hx1 (Subtype.ext h), ?_⟩
  exact (x.2.2 (r : X) (by simp)).symm

theorem autMAt_of_card_le_nine {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {N T : Subgroup X}
    (hcard : ∀ R : Subgroup X, R ≤ N → (∀ x ∈ R, x ^ 3 = 1) → Nat.card R ≤ 9)
    (hT : IsPGroup p T) (hT1 : T ≠ ⊥) (hTN : T ≤ N)
    (hNT : N ≤ Subgroup.normalizer (T : Set X))
    (hG : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizerHasPElementOutside p N) :
    AutMAt p N := by
  intro R hRN hexp h9
  have hR9 : Nat.card R = 9 := le_antisymm (hcard R hRN hexp) h9
  have hp3 : p ≠ 3 := by omega
  obtain ⟨r, hrR, hr1, x, hxT, hx1, hxr⟩ :=
    exists_commute_of_card_eq_nine hp3 hexp hR9 hT hT1 (hRN.trans hNT)
  have hro : orderOf r = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hexp r hrR) hr1
  obtain ⟨c, hcF, hcr, hcp, hcN⟩ :=
    hG x r (hTN hxT) (hRN hrR) hx1 (hT.to_le (Subgroup.zpowers_le.mpr hxT))
      (by rw [hro]; exact Nat.prime_three)
      (by rw [hro]; norm_num)
      (by rw [hro]; exact fun h => hp3 h.symm)
      hxr
  exact ⟨hR9, r, hrR, hr1, c, hcF, hcr, hcp, hcN⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAut
