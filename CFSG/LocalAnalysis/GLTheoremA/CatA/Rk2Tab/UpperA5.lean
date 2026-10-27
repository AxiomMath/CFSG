module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ClassicalModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15

theorem evenRank_le_of_pRank_top_le {G : Type*} [Group G] [Finite G] {k : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup G) ≤ k) :
    evenRank G ≤ k := by
  refine CFSG.RankThree.Coprime.evenRank_le_of_pRank_le fun p hp hp2 => ?_
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact h p hp hp2

theorem rkLin_SL6_four_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    rkLin 6 true 4 p 1 ≤ 4 := by
  by_cases hp3 : p = 3
  · subst hp3
    exact le_of_eq rkLin_SL6_4_r3_z1
  · have hep : eP 4 p ≠ 1 := by
      intro h
      rw [eP_eq_one_iff (Q := 4) (r := p) (by norm_num)] at h
      have h3 : p ∣ 3 := by simpa using h
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
    have hpos : 0 < eP 4 p := by
      rw [show eP 4 p = rk2Ord p 2 by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, eP_two_pow]]
      exact rk2Ord_pos hp hp2 2
    have h2 : 2 ≤ eP 4 p := by omega
    have hle : 6 / eP 4 p ≤ 3 := by
      have h : 6 / eP 4 p ≤ 6 / 2 := Nat.div_le_div_left (a := 6) h2 (by norm_num)
      have h' : 6 / 2 = 3 := by norm_num
      omega
    unfold rkLin
    simp only [if_true]
    rw [if_neg hep]
    omega

section


theorem rk2_up_a5 (hG : CFSG.Open.GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    {lab : GLALabel} (hK : Rk2IsLabel K lab) (hlab : lab = ⟨.A, 5, 2⟩)
    (hc : Subgroup.center K = ⊥) : evenRank K ≤ 4 := by
  subst hlab
  apply evenRank_le_of_pRank_top_le
  intro p hp hp2
  have hC : LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  have hA1 : (⟨.A, 5, 2⟩ : GLALabel).tag = .A → (⟨.A, 5, 2⟩ : GLALabel).rank = 1 → 3 ≤ 2 := by
    decide
  have hA2 : (⟨.A, 5, 2⟩ : GLALabel).tag = .A → (⟨.A, 5, 2⟩ : GLALabel).rank = 2 → 2 ≤ 2 := by
    decide
  have hA3 : (⟨.A, 5, 2⟩ : GLALabel).tag = .A → (⟨.A, 5, 2⟩ : GLALabel).rank = 3 → 2 ≤ 2 := by
    decide
  have hD3 : (⟨.A, 5, 2⟩ : GLALabel).tag = .D → (⟨.A, 5, 2⟩ : GLALabel).rank = 3 → 2 ≤ 2 := by
    decide
  have hTD2 : (⟨.A, 5, 2⟩ : GLALabel).tag = .twD → (⟨.A, 5, 2⟩ : GLALabel).rank = 2 → 2 ≤ 2 := by
    decide
  rw [rk2_pRank_eq_of_isLabel_classical hC hK hp hp2 (Or.inl rfl) hA1 hA2 hA3 hD3 hTD2]
  rw [hc, Subgroup.card_bot]
  have hchev : rk2Chev (⟨.A, 5, 2⟩ : GLALabel) p 1 = rkLin 6 true 4 p 1 := by
    simp [rk2Chev]
  rw [hchev]
  exact rkLin_SL6_four_le hp hp2

end

end CFSG.LocalAnalysis.GLTheoremA
