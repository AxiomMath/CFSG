module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

theorem rk3CasesOther_card {Q : TauCeti.PrimePower} (hQ : Q.p = 2) :
    Q.card = 2 ^ Q.exponent := by
  rw [TauCeti.PrimePower.card_def, hQ]

theorem rk3CasesOther_eS {Q : TauCeti.PrimePower} (hQ : Q.p = 2) : eS Q.card 3 = 1 := by
  rw [rk3CasesOther_card hQ]
  exact eS_two_pow_three _

theorem rk3CasesOther_eP {Q : TauCeti.PrimePower} (hQ : Q.p = 2) :
    eP Q.card 3 = if Even Q.exponent then 1 else 2 := by
  rw [rk3CasesOther_card hQ]
  exact eP_two_pow_three _

theorem rk3CasesOther_eP_dvd_four {Q : TauCeti.PrimePower} (hQ : Q.p = 2) :
    eP Q.card 3 ∣ 4 := by
  rw [rk3CasesOther_eP hQ]
  split_ifs <;> norm_num

theorem rk3CasesOther_mRank_B {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) :
    mRankChev (.B l Q) 3 z = l := by
  show rkSp l Q.card 3 = l
  unfold rkSp
  rw [rk3CasesOther_eS hQ, Nat.div_one]

theorem rk3CasesOther_mRank_G2 {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) :
    mRankChev (.G2 Q) 3 z = 2 := by
  show rkG2 Q.card 3 = 2
  rw [rkG2, rk3CasesOther_eS hQ, if_pos rfl]

theorem rk3CasesOther_mRank_D {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 4 ≤ l)
    (z : ℕ) : 4 ≤ mRankChev (.D l Q) 3 z := by
  show 4 ≤ rkOmPlus l Q.card 3
  unfold rkOmPlus
  rw [rk3CasesOther_eS hQ, rk3CasesOther_eP hQ]
  by_cases hn : Even Q.exponent
  · rw [if_pos hn]
    split_ifs <;> omega
  · rw [if_neg hn]
    split_ifs <;> omega

theorem rk3CasesOther_mRank_tD {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) :
    mRankChev (.twistedD l Q) 3 z = l - (if eP Q.card 3 ∣ l then 1 else 0) := by
  show rkOmMinus l Q.card 3 = l - (if eP Q.card 3 ∣ l then 1 else 0)
  unfold rkOmMinus
  rw [rk3CasesOther_eS hQ, Nat.div_one]

theorem rk3CasesOther_mRank_tD_four {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) :
    mRankChev (.twistedD 4 Q) 3 z = 3 := by
  have h := rk3CasesOther_mRank_tD (l := 4) hQ z
  rw [if_pos (rk3CasesOther_eP_dvd_four hQ)] at h
  omega

theorem rk3CasesOther_mRank_tD_ge {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 5 ≤ l)
    (z : ℕ) : 4 ≤ mRankChev (.twistedD l Q) 3 z := by
  rw [rk3CasesOther_mRank_tD hQ z]
  split_ifs <;> omega

theorem rk3CasesOther_notOne_B (l : ℕ) (Q : TauCeti.PrimePower) : ¬ RankOneList (.B l Q) := by
  simp [RankOneList]

theorem rk3CasesOther_RankTwo_B (l : ℕ) (Q : TauCeti.PrimePower) :
    RankTwoList (.B l Q) ↔ l = 2 := by
  by_cases h : l = 2
  · subst h
    simp [RankTwoList]
  · simp [RankTwoList, h]

theorem rk3CasesOther_RankThree_B (l : ℕ) (Q : TauCeti.PrimePower) :
    RankThreeList (.B l Q) ↔ l = 3 := by
  by_cases h : l = 3
  · subst h
    simp [RankThreeList]
  · simp [RankThreeList, h]

theorem rk3CasesOther_notOne_D (l : ℕ) (Q : TauCeti.PrimePower) : ¬ RankOneList (.D l Q) := by
  simp [RankOneList]

theorem rk3CasesOther_notTwo_D (l : ℕ) (Q : TauCeti.PrimePower) : ¬ RankTwoList (.D l Q) := by
  simp [RankTwoList]

theorem rk3CasesOther_notThree_D (l : ℕ) (Q : TauCeti.PrimePower) : ¬ RankThreeList (.D l Q) := by
  simp [RankThreeList]

theorem rk3CasesOther_notOne_tD (l : ℕ) (Q : TauCeti.PrimePower) :
    ¬ RankOneList (.twistedD l Q) := by
  simp [RankOneList]

theorem rk3CasesOther_notTwo_tD (l : ℕ) (Q : TauCeti.PrimePower) :
    ¬ RankTwoList (.twistedD l Q) := by
  simp [RankTwoList]

theorem rk3CasesOther_RankThree_tD (l : ℕ) (Q : TauCeti.PrimePower) :
    RankThreeList (.twistedD l Q) ↔ l = 4 := by
  by_cases h : l = 4
  · subst h
    simp [RankThreeList]
  · simp [RankThreeList, h]

theorem rk3CasesOther_RankTwo_G2 (Q : TauCeti.PrimePower) : RankTwoList (.G2 Q) := by
  simp [RankTwoList]

theorem rk3CasesOther_notOne_G2 (Q : TauCeti.PrimePower) : ¬ RankOneList (.G2 Q) := by
  simp [RankOneList]

theorem rk3CasesOther_notThree_G2 (Q : TauCeti.PrimePower) : ¬ RankThreeList (.G2 Q) := by
  simp [RankThreeList]

theorem rk3CasesOther_ge4 {d : TauCeti.LieTypeIndex} {z : ℕ} (hv : 4 ≤ mRankChev d 3 z)
    (h1 : ¬ RankOneList d) (h2 : ¬ RankTwoList d) (h3 : ¬ RankThreeList d) : Rk3Cases d z := by
  unfold Rk3Cases
  exact ⟨⟨fun h => absurd h (by omega), fun h => absurd h h1⟩,
    ⟨fun h => absurd h (by omega), fun h => absurd h h2⟩,
    ⟨fun h => absurd h (by omega), fun h => absurd h h3⟩,
    Or.inr (Or.inr (Or.inr hv))⟩

theorem rk3CasesOther_two {d : TauCeti.LieTypeIndex} {z : ℕ} (hv : mRankChev d 3 z = 2)
    (h2 : RankTwoList d) (h1 : ¬ RankOneList d) (h3 : ¬ RankThreeList d) : Rk3Cases d z := by
  unfold Rk3Cases
  exact ⟨⟨fun h => absurd h (by omega), fun h => absurd h h1⟩,
    ⟨fun _ => h2, fun _ => hv⟩,
    ⟨fun h => absurd h (by omega), fun h => absurd h h3⟩,
    Or.inr (Or.inl h2)⟩

theorem rk3CasesOther_three {d : TauCeti.LieTypeIndex} {z : ℕ} (hv : mRankChev d 3 z = 3)
    (h3 : RankThreeList d) (h1 : ¬ RankOneList d) (h2 : ¬ RankTwoList d) : Rk3Cases d z := by
  unfold Rk3Cases
  exact ⟨⟨fun h => absurd h (by omega), fun h => absurd h h1⟩,
    ⟨fun h => absurd h (by omega), fun h => absurd h h2⟩,
    ⟨fun _ => h3, fun _ => hv⟩,
    Or.inr (Or.inr (Or.inl h3))⟩

theorem rk3Cases_B {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 2 ≤ l) (z : ℕ) :
    Rk3Cases (.B l Q) z := by
  have hv := rk3CasesOther_mRank_B (l := l) hQ z
  have h1 := rk3CasesOther_notOne_B l Q
  have h2 := rk3CasesOther_RankTwo_B l Q
  have h3 := rk3CasesOther_RankThree_B l Q
  rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with h | h | h
  · exact rk3CasesOther_two (hv.trans h) (h2.mpr h) h1 (fun h' => by have := h3.mp h'; omega)
  · exact rk3CasesOther_three (hv.trans h) (h3.mpr h) h1 (fun h' => by have := h2.mp h'; omega)
  · exact rk3CasesOther_ge4 (by omega) h1 (fun h' => by have := h2.mp h'; omega)
      (fun h' => by have := h3.mp h'; omega)

theorem rk3Cases_D {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 4 ≤ l) (z : ℕ) :
    Rk3Cases (.D l Q) z :=
  rk3CasesOther_ge4 (rk3CasesOther_mRank_D hQ hl z) (rk3CasesOther_notOne_D l Q)
    (rk3CasesOther_notTwo_D l Q) (rk3CasesOther_notThree_D l Q)

theorem rk3Cases_tD {l : ℕ} {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (hl : 4 ≤ l) (z : ℕ) :
    Rk3Cases (.twistedD l Q) z := by
  rcases (show l = 4 ∨ 5 ≤ l by omega) with h | h
  · subst h
    exact rk3CasesOther_three (rk3CasesOther_mRank_tD_four hQ z)
      ((rk3CasesOther_RankThree_tD 4 Q).mpr rfl) (rk3CasesOther_notOne_tD 4 Q)
      (rk3CasesOther_notTwo_tD 4 Q)
  · exact rk3CasesOther_ge4 (rk3CasesOther_mRank_tD_ge hQ h z) (rk3CasesOther_notOne_tD l Q)
      (rk3CasesOther_notTwo_tD l Q)
      (fun h' => by have := (rk3CasesOther_RankThree_tD l Q).mp h'; omega)

theorem rk3Cases_G2 {Q : TauCeti.PrimePower} (hQ : Q.p = 2) (z : ℕ) : Rk3Cases (.G2 Q) z :=
  rk3CasesOther_two (rk3CasesOther_mRank_G2 hQ z) (rk3CasesOther_RankTwo_G2 Q)
    (rk3CasesOther_notOne_G2 Q) (rk3CasesOther_notThree_G2 Q)

end CFSG.LocalAnalysis.RankThreeUC.S15
