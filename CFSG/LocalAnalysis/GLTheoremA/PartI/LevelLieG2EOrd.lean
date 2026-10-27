module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2EBd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.I1420 Finset

@[expose] def Nbig : ℕ := 2 ^ 18 * (3 ^ 5 * 7 ^ 2 * 13 * 19 * 73)

theorem odd_cof : Odd (3 ^ 5 * 7 ^ 2 * 13 * 19 * 73) := by decide

theorem gridA : ∀ n ∈ ([1, 2, 3, 4, 5] : List ℕ), ∀ k ∈ (List.range 19), 1 ≤ k →
    orderA n (2 ^ k) ∣ Nbig →
      (n = 1 ∧ (k = 1 ∨ k = 3 ∨ k = 9)) ∨ (n = 2 ∧ (k = 1 ∨ k = 3)) := by
  unfold Nbig
  decide +kernel

theorem gridTA : ∀ n ∈ ([2, 3, 4, 5] : List ℕ), ∀ k ∈ (List.range 19), 1 ≤ k →
    orderTwistedA n (2 ^ k) ∣ Nbig → n = 2 ∧ (k = 1 ∨ k = 3) := by
  unfold Nbig
  decide +kernel

theorem gridBC : ∀ n ∈ ([2, 3, 4] : List ℕ), ∀ k ∈ (List.range 19), 1 ≤ k →
    ¬ orderBC n (2 ^ k) ∣ Nbig := by
  unfold Nbig
  decide +kernel

theorem gridD : ∀ k ∈ (List.range 19), 1 ≤ k → ¬ orderD 4 (2 ^ k) ∣ Nbig := by
  unfold Nbig
  decide +kernel

theorem gridTD : ∀ k ∈ (List.range 19), 1 ≤ k → ¬ orderTwistedD 4 (2 ^ k) ∣ Nbig := by
  unfold Nbig
  decide +kernel

theorem gridG2 : ∀ k ∈ (List.range 19), 1 ≤ k → orderG2 (2 ^ k) ∣ Nbig → k = 1 ∨ k = 3 := by
  unfold Nbig
  decide +kernel

theorem gridT4 : ∀ k ∈ (List.range 19), 1 ≤ k → orderTrialityD4 (2 ^ k) ∣ Nbig → k = 1 := by
  unfold Nbig
  decide +kernel

theorem gridSz : ∀ k ∈ (List.range 19), 1 ≤ k → ¬ orderSuzuki (2 ^ k) ∣ Nbig := by
  unfold Nbig
  decide +kernel

theorem not_tits : ¬ orderTits ∣ Nbig := by
  unfold orderTits Nbig
  decide +kernel


open TauCeti in
theorem classify {d : LieTypeIndex} (hv : d.Valid) (hc : d.characteristic = 2)
    (h : lieOrderFormula d ∣ Nbig) :
    (∃ q : PrimePower, d = .A 1 q ∧ (q.card = 8 ∨ q.card = 512)) ∨
    (∃ q : PrimePower, d = .A 2 q ∧ q.card = 8) ∨
    (∃ q : PrimePower, d = .twistedA 2 q ∧ q.card = 8) ∨
    (∃ q : PrimePower, d = .G2 q ∧ q.card = 8) ∨
    (∃ q : PrimePower, d = .trialityD4 q ∧ q.card = 2) := by
  have hm := odd_cof
  have hs : d.InStandardRange := ((LieTypeIndex.valid_iff d).1 hv).1
  have hdup : ¬ d.IsDuplicateRepresentative := ((LieTypeIndex.valid_iff d).1 hv).2
  rw [LieTypeIndex.inStandardRange_iff] at hs
  rw [LieTypeIndex.isDuplicateRepresentative_iff] at hdup
  have hN : Nbig = 2 ^ 18 * (3 ^ 5 * 7 ^ 2 * 13 * 19 * 73) := rfl
  cases d with
  | A n q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderA n (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderA_bound (a := 18) hm hs.1 hk (hN ▸ h')
    have hn5 : n ≤ 5 := by
      by_contra hcon
      push Not at hcon
      have : 6 * 7 ≤ n * (n + 1) := Nat.mul_le_mul hcon (by omega)
      have h2 : 21 ≤ n * (n + 1) / 2 := by omega
      nlinarith
    have hk18 : q.exponent ≤ 18 := by
      have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith [hs.1]) (by norm_num)
      nlinarith
    rcases gridA n (by simp; omega) q.exponent (by simp; omega) hk h' with
      ⟨rfl, hk1 | hk3 | hk9⟩ | ⟨rfl, hk1 | hk3⟩
    · exact absurd (by rw [hq, hk1]; norm_num : q.card = 2) (by
        intro hc2; have := hs.2 rfl; omega)
    · exact Or.inl ⟨q, rfl, Or.inl (by rw [hq, hk3]; norm_num)⟩
    · exact Or.inl ⟨q, rfl, Or.inr (by rw [hq, hk9]; norm_num)⟩
    · exact absurd (Or.inr (Or.inl ⟨rfl, by rw [hq, hk1]; norm_num⟩)) hdup
    · exact Or.inr (Or.inl ⟨q, rfl, by rw [hq, hk3]; norm_num⟩)
  | twistedA n q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderTwistedA n (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderTwistedA_bound (a := 18) hm (by omega : 1 ≤ n) hk (hN ▸ h')
    have hn5 : n ≤ 5 := by
      by_contra hcon
      push Not at hcon
      have : 6 * 7 ≤ n * (n + 1) := Nat.mul_le_mul hcon (by omega)
      have h2 : 21 ≤ n * (n + 1) / 2 := by omega
      nlinarith
    have hk18 : q.exponent ≤ 18 := by
      have : 1 ≤ n * (n + 1) / 2 := Nat.div_pos (by nlinarith [hs.1]) (by norm_num)
      nlinarith
    obtain ⟨rfl, hk1 | hk3⟩ := gridTA n (by simp; omega) q.exponent (by simp; omega) hk h'
    · exact absurd (by rw [hq, hk1]; norm_num : q.card = 2) (by
        intro hc2; have := hs.2 rfl; omega)
    · exact Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hq, hk3]; norm_num⟩))
  | B n q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderBC n (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderBC_bound (a := 18) hm (by omega : 1 ≤ n) hk (hN ▸ h')
    have hn2 : 2 ≤ n := hs.1
    have hn4 : n ≤ 4 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    have hk18 : q.exponent ≤ 18 := by
      have : q.exponent ≤ q.exponent * (n * n) := Nat.le_mul_of_pos_right _ (by nlinarith)
      omega
    exact absurd h' (gridBC n (by simp; omega) q.exponent (by simp; omega) hk)
  | C n q =>
    have hp : q.p = 2 := by simpa using hc
    exact absurd hp hs.2
  | D n q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderD n (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderD_bound (a := 18) hm hs hk (hN ▸ h')
    have hn4 : n = 4 := by
      by_contra hcon
      have h5 : 5 ≤ n := by omega
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul h5 (by omega)
      nlinarith
    subst hn4
    have hk18 : q.exponent ≤ 18 := by
      have : q.exponent ≤ q.exponent * (4 * (4 - 1)) := Nat.le_mul_of_pos_right _ (by norm_num)
      omega
    exact absurd h' (gridD q.exponent (by simp; omega) hk)
  | twistedD n q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderTwistedD n (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderTwistedD_bound (a := 18) hm hs hk (hN ▸ h')
    have hn4 : n = 4 := by
      by_contra hcon
      have h5 : 5 ≤ n := by omega
      have : 5 * 4 ≤ n * (n - 1) := Nat.mul_le_mul h5 (by omega)
      nlinarith
    subst hn4
    have hk18 : q.exponent ≤ 18 := by
      have : q.exponent ≤ q.exponent * (4 * (4 - 1)) := Nat.le_mul_of_pos_right _ (by norm_num)
      omega
    exact absurd h' (gridTD q.exponent (by simp; omega) hk)
  | E6 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderE6 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have := orderE6_bound (a := 18) hm hk (hN ▸ h')
    omega
  | E7 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderE7 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have := orderE7_bound (a := 18) hm hk (hN ▸ h')
    omega
  | E8 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderE8 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have := orderE8_bound (a := 18) hm hk (hN ▸ h')
    omega
  | F4 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderF4 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have := orderF4_bound (a := 18) hm hk (hN ▸ h')
    omega
  | G2 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderG2 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderG2_bound (a := 18) hm hk (hN ▸ h')
    have hk18 : q.exponent ≤ 18 := by omega
    rcases gridG2 q.exponent (by simp; omega) hk h' with hk1 | hk3
    · exact absurd (by rw [hq, hk1]; norm_num : q.card = 2) (by
        intro hc2; have := hs; omega)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, by rw [hq, hk3]; norm_num⟩)))
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderTwistedE6 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have := orderTwistedE6_bound (a := 18) hm hk (hN ▸ h')
    omega
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hc
    have hk : 1 ≤ q.exponent := q.exponent_pos
    have hq : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
    have h' : orderTrialityD4 (2 ^ q.exponent) ∣ Nbig := by
      have := h
      simp only [lieOrderFormula, hq] at this
      exact this
    have hb := orderTrialityD4_bound (a := 18) hm hk (hN ▸ h')
    have hk18 : q.exponent ≤ 18 := by omega
    have hk1 := gridT4 q.exponent (by simp; omega) hk h'
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl, by rw [hq, hk1]; norm_num⟩)))
  | suzuki m =>
    have hk : 1 ≤ 2 * m + 1 := by omega
    have h' : orderSuzuki (2 ^ (2 * m + 1)) ∣ Nbig := h
    have hb := orderSuzuki_bound (a := 18) hm hk (hN ▸ h')
    have hk18 : 2 * m + 1 ≤ 18 := by omega
    exact absurd h' (gridSz (2 * m + 1) (by simp; omega) hk)
  | reeG2 m => simp at hc
  | reeF4 m =>
    have hm1 : 1 ≤ m := hs
    have hk : 1 ≤ 2 * m + 1 := by omega
    have h' : orderTwistedF4 (2 ^ (2 * m + 1)) ∣ Nbig := h
    have hb := orderTwistedF4_bound (a := 18) hm hk (hN ▸ h')
    omega
  | tits => exact absurd h not_tits

end CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
