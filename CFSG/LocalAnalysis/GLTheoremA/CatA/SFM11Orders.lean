module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05NonIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM11

section Cert

theorem orderEq_B3 {H : Type} [Group H] {t : CFSG.Open.StatedLieTag} {p f : ℕ}
    (hb : CFSG.Blueprint.LieModel H t 3 p f) (ht : t = .PSp ∨ t = .POmegaOdd) :
    ∃ d : ℕ, d ∣ 4 ∧ 1 ≤ d ∧
      Nat.card H * d = (p ^ f) ^ 9 * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1))) ∧
      (Nat.card H).factorization p = 9 * f := by
  obtain ⟨h1, h2⟩ := YS05NonIso.raw_eq hb
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator t 3 (p ^ f) =
      (p ^ f) ^ 9 * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1))) := by
    rcases ht with rfl | rfl
    · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
      rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
        Finset.prod_pair (by decide)]
      norm_num
    · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
      rw [show Finset.Icc 1 3 = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
        Finset.prod_pair (by decide)]
      norm_num
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t 3 (p ^ f) ∣ 4 ∧
      1 ≤ CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t 3 (p ^ f) := by
    rcases ht with rfl | rfl
    · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor]
      exact ⟨(Nat.gcd_dvd_left _ _).trans (by norm_num), Nat.gcd_pos_of_pos_left _ (by norm_num)⟩
    · simp only [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor]
      exact ⟨by norm_num, by norm_num⟩
  refine ⟨CFSG.ComponentClassification.CatLeaf.lieOrderDivisor t 3 (p ^ f), hdiv.1, hdiv.2, ?_, ?_⟩
  · rw [h1, hnum]
  · rw [h2]
    rcases ht with rfl | rfl
    · simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
    · simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]

theorem orderEq_D4 {H : Type} [Group H] {p f : ℕ} (hb : CFSG.Blueprint.LieModel H .POmegaPlus 4 p f) :
    ∃ d : ℕ, d ∣ 4 ∧ 1 ≤ d ∧
      Nat.card H * d = (p ^ f) ^ 12 * (((p ^ f) ^ 4 - 1) *
        (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1)))) ∧
      (Nat.card H).factorization p = 12 * f := by
  obtain ⟨h1, h2⟩ := YS05NonIso.raw_eq hb
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .POmegaPlus 4 (p ^ f) =
      (p ^ f) ^ 12 * (((p ^ f) ^ 4 - 1) * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1)))) := by
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
    rw [show Finset.Icc 1 (4 - 1) = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
    norm_num
    ring
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .POmegaPlus 4 (p ^ f) =
      Nat.gcd 4 ((p ^ f) ^ 4 - 1) := rfl
  refine ⟨Nat.gcd 4 ((p ^ f) ^ 4 - 1), Nat.gcd_dvd_left _ _,
    Nat.gcd_pos_of_pos_left _ (by norm_num), ?_, ?_⟩
  · rw [← hdiv, h1, hnum]
  · rw [h2]
    simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]

theorem orderEq_D2_4 {H : Type} [Group H] {p f : ℕ} (hb : CFSG.Blueprint.LieModel H .POmegaMinus 4 p f) :
    ∃ d : ℕ, d ∣ 4 ∧ 1 ≤ d ∧
      Nat.card H * d = (p ^ f) ^ 12 * (((p ^ f) ^ 4 + 1) *
        (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1)))) ∧
      (Nat.card H).factorization p = 12 * f := by
  obtain ⟨h1, h2⟩ := YS05NonIso.raw_eq hb
  have hnum : CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .POmegaMinus 4 (p ^ f) =
      (p ^ f) ^ 12 * (((p ^ f) ^ 4 + 1) * (((p ^ f) ^ 2 - 1) * (((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 6 - 1)))) := by
    simp only [CFSG.ComponentClassification.CatLeaf.lieOrderNumerator]
    rw [show Finset.Icc 1 (4 - 1) = {1, 2, 3} from by decide, Finset.prod_insert (by decide),
      Finset.prod_pair (by decide)]
    norm_num
    ring
  have hdiv : CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .POmegaMinus 4 (p ^ f) =
      Nat.gcd 4 ((p ^ f) ^ 4 + 1) := rfl
  refine ⟨Nat.gcd 4 ((p ^ f) ^ 4 + 1), Nat.gcd_dvd_left _ _,
    Nat.gcd_pos_of_pos_left _ (by norm_num), ?_, ?_⟩
  · rw [← hdiv, h1, hnum]
  · rw [h2]
    simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]

end Cert

end CFSG.LocalAnalysis.GLTheoremA.SFM11
