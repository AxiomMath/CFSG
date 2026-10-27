module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviU4Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)

variable {m : ℕ} {K : Type} [Field K]

theorem card_sub_one_eq (h : UnitaryFieldData 2 m K) :
    Nat.card K - 1 = (2 ^ m - 1) * (2 ^ m + 1) := by
  have hq : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 1 := ⟨2 ^ m - 1, by omega⟩
  rw [h.card, pow_mul', hr]
  have : (r + 1) ^ 2 = r * (r + 1 + 1) + 1 := by ring
  simp only [Nat.add_sub_cancel]
  omega

theorem exists_prime_two_le_pRank_hypSU (h : UnitaryFieldData 2 m K) :
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ∣ Nat.card K - 1 ∧
      2 ≤ CFSG.Open.pRank f (⊤ : Subgroup (hypSU h 2 0)) := by
  have hm : 1 ≤ m := h.one_le
  have hm4 : 4 ≤ Nat.card K := by
    rw [h.card]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2dvd : 2 ∣ Nat.card K := by
    rw [h.card]
    exact dvd_pow_self 2 (by omega)
  have hne : Nat.card K - 1 ≠ 1 := by omega
  obtain ⟨f, hf, hfd⟩ := Nat.exists_prime_and_dvd hne
  have hf2 : f ≠ 2 := by
    rintro rfl
    omega
  haveI : Fact f.Prime := ⟨hf⟩
  have hdiv : f ∣ (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [← card_sub_one_eq h]
    exact hfd
  rcases (Nat.Prime.dvd_mul hf).1 hdiv with h1 | h1
  · exact ⟨f, hf, hf2, hfd, hypSU_two_le_pRank_of_dvd_sub h hf2 h1⟩
  · exact ⟨f, hf, hf2, hfd, hypSU_two_le_pRank_of_dvd_add h hf2 h1⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
