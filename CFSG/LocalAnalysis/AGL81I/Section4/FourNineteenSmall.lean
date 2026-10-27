module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTable

public section

namespace CFSG.LocalAnalysis.AGL81I.Section4

open CFSG.LocalAnalysis.RankThreeUC.S15

theorem pRank_add_one_le_of_alt (h : LieOddRankAlt) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 8)
    (e : Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin n)) {d : ℕ} (hd : d.Prime)
    (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) + 1 ≤
      max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y)) := by
  have hn5 : 5 ≤ n := by omega
  have h3 := h Y hY n hn5 ⟨e⟩ 3 Nat.prime_three (by norm_num)
  have hd3 : d ≠ 3 := by omega
  have hp := h Y hY n hn5 ⟨e⟩ d hd (by omega)
  have hdiv : n / d ≤ 1 := by
    rw [Nat.div_le_iff_le_mul (by omega : 0 < d)]
    omega
  rw [h3, hp]
  rcases hn with rfl | rfl | rfl <;> norm_num at hdiv ⊢ <;> omega

theorem pRank_add_one_le_of_psl_seven (h : LieOddRankSmall) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (q : TauCeti.PrimePower)
    (d : TauCeti.ValidLieTypeIndex) (hq : q.card = 7) (hd : d.1 = .A 1 q)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) + 1 ≤
      max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y)) := by
  have h3 := (h Y hY 3 Nat.prime_three (by norm_num)).1
    ⟨q, d, hq, hd, ⟨e⟩⟩
  have hp3 : p ≠ 3 := by omega
  have hp' := (h Y hY p hp (by omega)).1 ⟨q, d, hq, hd, ⟨e⟩⟩
  rw [h3, hp']
  by_cases hp7 : p = 7
  · simp [hp7]
  · simp [hp3, hp7]

theorem pRank_add_one_le_of_psu_three (h : LieOddRankSmall) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (q : TauCeti.PrimePower)
    (d : TauCeti.ValidLieTypeIndex) (hq : q.card = 3) (hd : d.1 = .twistedA 2 q)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) + 1 ≤
      max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y)) := by
  have h3 := (h Y hY 3 Nat.prime_three (by norm_num)).2
    ⟨q, d, hq, hd, ⟨e⟩⟩
  have hp3 : p ≠ 3 := by omega
  have hp' := (h Y hY p hp (by omega)).2 ⟨q, d, hq, hd, ⟨e⟩⟩
  rw [h3, hp']
  by_cases hp7 : p = 7
  · simp [hp7]
  · simp [hp3, hp7]

theorem pRank_add_one_le_of_small (h : LieOddRankSmall) {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (d : TauCeti.ValidLieTypeIndex)
    (hd : (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
      ∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)
    (e : Y ⧸ Subgroup.center Y ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) + 1 ≤
      max 2 (CFSG.Open.pRank 3 (⊤ : Subgroup Y)) := by
  rcases hd with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩
  · exact pRank_add_one_le_of_psl_seven h hY q d hq hd e hp hp5
  · exact pRank_add_one_le_of_psu_three h hY q d hq hd e hp hp5

end CFSG.LocalAnalysis.AGL81I.Section4

end
