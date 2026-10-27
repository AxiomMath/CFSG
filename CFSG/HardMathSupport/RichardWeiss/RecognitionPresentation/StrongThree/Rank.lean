module

import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem le_pRank {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

theorem exists_isElemAbelian_card_pRank {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ pRank p H :=
  CFSG.SectionRank.exists_pRank hp.one_lt H

theorem three_dvd_card_of_one_le_pRank {R : Subgroup G} (h : 1 ≤ pRank 3 R) : 3 ∣ Nat.card R := by
  obtain ⟨E, hER, -, hE⟩ := exists_isElemAbelian_card_pRank Nat.prime_three R
  have : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 (by omega)
  exact this.trans (Subgroup.card_dvd_of_le hER)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
