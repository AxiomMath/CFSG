module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem rk3Cases_A_aux_rankOne (l : ℕ) (Q : TauCeti.PrimePower) :
    RankOneList (.A l Q) ↔ l = 2 ∧ Odd Q.exponent := by
  rcases l with _ | _ | _ | l <;> simp [RankOneList]

theorem rk3Cases_A_aux_rankTwo (l : ℕ) (Q : TauCeti.PrimePower) :
    RankTwoList (.A l Q) ↔ (l = 2 ∧ Even Q.exponent) ∨ (l = 3 ∧ Odd Q.exponent) ∨
      (l = 4 ∧ Odd Q.exponent) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp [RankTwoList]

theorem rk3Cases_A_aux_rankThree (l : ℕ) (Q : TauCeti.PrimePower) :
    RankThreeList (.A l Q) ↔ (l = 3 ∧ Even Q.exponent) ∨ (l = 5 ∧ Odd Q.exponent) ∨
      (l = 6 ∧ Odd Q.exponent) := by
  rcases l with _ | _ | _ | _ | _ | _ | _ | l <;> simp [RankThreeList]

theorem rk3Cases_tA_aux_rankOne (l : ℕ) (Q : TauCeti.PrimePower) :
    ¬ RankOneList (.twistedA l Q) := by
  simp [RankOneList]

theorem rk3Cases_tA_aux_rankTwo (l : ℕ) (Q : TauCeti.PrimePower) :
    RankTwoList (.twistedA l Q) ↔ (l = 2 ∧ Odd Q.exponent) ∨ (l = 3 ∧ Even Q.exponent) ∨
      (l = 4 ∧ Even Q.exponent) := by
  rcases l with _ | _ | _ | _ | _ | l <;> simp [RankTwoList]

theorem rk3Cases_tA_aux_rankThree (l : ℕ) (Q : TauCeti.PrimePower) :
    RankThreeList (.twistedA l Q) ↔ (l = 3 ∧ Odd Q.exponent) ∨ (l = 5 ∧ Even Q.exponent) ∨
      (l = 6 ∧ Even Q.exponent) := by
  rcases l with _ | _ | _ | _ | _ | _ | _ | l <;> simp [RankThreeList]

theorem rk3Cases_A_aux_rkLin_one (m : ℕ) (eps : Bool) (Q z : ℕ)
    (h : (if eps then eP Q 3 else eM Q 3) = 1) :
    ∃ δ : ℕ, δ ≤ 1 ∧ (δ = 1 → 3 ∣ m ∧ 4 ≤ m) ∧ rkLin m eps Q 3 z = m - 1 - δ := by
  unfold rkLin
  rw [if_pos h]
  by_cases hc : ¬ 3 ∣ z ∧ 3 ∣ m ∧ 4 ≤ m ∧
      padicValNat 3 (if eps then Q - 1 else Q + 1) ≤ padicValNat 3 m
  · exact ⟨1, le_rfl, fun _ => ⟨hc.2.1, hc.2.2.1⟩, by rw [if_pos hc]⟩
  · exact ⟨0, by omega, fun h => by omega, by rw [if_neg hc]⟩

theorem rk3Cases_A_aux_rkLin_two (m : ℕ) (eps : Bool) (Q z : ℕ)
    (h : (if eps then eP Q 3 else eM Q 3) = 2) :
    rkLin m eps Q 3 z = m / 2 := by
  unfold rkLin
  rw [if_neg (by omega), h]

theorem rk3Cases_A {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 2 ≤ l) (z : ℕ) :
    Rk3Cases (.A l Q) z := by
  have hc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hm : mRankChev (.A l Q) 3 z = rkLin (l + 1) true (2 ^ Q.exponent) 3 z := by
    rw [← hc]; rfl
  unfold Rk3Cases
  rw [hm, rk3Cases_A_aux_rankOne, rk3Cases_A_aux_rankTwo, rk3Cases_A_aux_rankThree]
  by_cases hn : Even Q.exponent
  · have hn' : ¬ Odd Q.exponent := Nat.not_odd_iff_even.mpr hn
    obtain ⟨δ, hδ1, hδ2, hv⟩ := rk3Cases_A_aux_rkLin_one (l + 1) true (2 ^ Q.exponent) z
      (by simp [eP_two_pow_three, hn])
    rw [hv]
    simp only [hn, hn', and_true, and_false, or_false, false_or, iff_false]
    omega
  · have hn' : Odd Q.exponent := Nat.not_even_iff_odd.mp hn
    have hv := rk3Cases_A_aux_rkLin_two (l + 1) true (2 ^ Q.exponent) z
      (by simp [eP_two_pow_three, hn])
    rw [hv]
    simp only [hn, hn', and_true, and_false, or_false, false_or, iff_false]
    omega

theorem rk3Cases_tA {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 3 ≤ l) (z : ℕ) :
    Rk3Cases (.twistedA l Q) z := by
  have hc : Q.card = 2 ^ Q.exponent := by rw [TauCeti.PrimePower.card_def, hQ]
  have hm : mRankChev (.twistedA l Q) 3 z = rkLin (l + 1) false (2 ^ Q.exponent) 3 z := by
    rw [← hc]; rfl
  unfold Rk3Cases
  rw [hm, rk3Cases_tA_aux_rankTwo, rk3Cases_tA_aux_rankThree]
  by_cases hn : Even Q.exponent
  · have hn' : ¬ Odd Q.exponent := Nat.not_odd_iff_even.mpr hn
    have hv := rk3Cases_A_aux_rkLin_two (l + 1) false (2 ^ Q.exponent) z
      (by simp [eM_two_pow_three, hn])
    rw [hv]
    simp only [rk3Cases_tA_aux_rankOne, hn, hn', and_true, and_false, or_false, false_or,
      iff_false]
    omega
  · have hn' : Odd Q.exponent := Nat.not_even_iff_odd.mp hn
    obtain ⟨δ, hδ1, hδ2, hv⟩ := rk3Cases_A_aux_rkLin_one (l + 1) false (2 ^ Q.exponent) z
      (by simp [eM_two_pow_three, hn])
    rw [hv]
    simp only [rk3Cases_tA_aux_rankOne, hn, hn', and_true, and_false, or_false, false_or,
      iff_false]
    omega

end CFSG.LocalAnalysis.RankThreeUC.S15
