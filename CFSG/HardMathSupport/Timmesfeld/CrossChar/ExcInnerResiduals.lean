module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSplit
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.Blueprint.Chevalley CFSG.TauCetiBridge

theorem orderOf_natCast_zmod_five {n : ℕ} (hn : ¬ 5 ∣ n) :
    orderOf ((n : ℕ) : ZMod 5) = 1 ∨ orderOf ((n : ℕ) : ZMod 5) = 2 ∨
      orderOf ((n : ℕ) : ZMod 5) = 4 := by
  have h0 : ((n : ℕ) : ZMod 5) ≠ 0 := fun h => hn ((ZMod.natCast_eq_zero_iff n 5).1 h)
  have h4 : ((n : ℕ) : ZMod 5) ^ 4 = 1 := by
    generalize ((n : ℕ) : ZMod 5) = x at h0 ⊢
    revert x
    decide
  have hd := orderOf_dvd_of_pow_eq_one h4
  have hle := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf ((n : ℕ) : ZMod 5) := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
    ⟨4, by norm_num, h4⟩)
  interval_cases h : orderOf ((n : ℕ) : ZMod 5) <;> simp_all

theorem five_dvd_sq_sub_one_iff {n : ℕ} (hn : ¬ 5 ∣ n) :
    5 ∣ n ^ 2 - 1 ↔ orderOf ((n : ℕ) : ZMod 5) = 1 ∨ orderOf ((n : ℕ) : ZMod 5) = 2 := by
  have hn1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero fun h0 => hn (h0 ▸ dvd_zero 5))
  have hcast : 5 ∣ n ^ 2 - 1 ↔ ((n : ℕ) : ZMod 5) ^ 2 = 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn1, Nat.cast_pow, Nat.cast_one, sub_eq_zero]
  rw [hcast]
  constructor
  · intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    have hpos : 0 < orderOf ((n : ℕ) : ZMod 5) := orderOf_pos_iff.2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨2, by norm_num, h⟩)
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases h' : orderOf ((n : ℕ) : ZMod 5) <;> simp_all
  · rintro (h | h)
    · rw [orderOf_eq_one_iff] at h
      rw [h, one_pow]
    · rw [← h]
      exact pow_orderOf_eq_one _

theorem crossCharInnerAt_E8_of_split
    (h3 : CrossCharInnerAt .E8 fun _ p => p = 3)
    (h5 : CrossCharInnerAt .E8 fun _ p => p = 5)
    (h7 : CrossCharInnerAt .E8 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p) :
    CrossCharInnerAt .E8 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E8 q ∧
      3 ≤ degCount Tag.E8 (orderOf ((q.card : ℕ) : ZMod p)) :=
  CrossCharInnerAt.of_split (fun idx hk p hp hp2 hc h => h3 idx hk p hp hp2 hc h.2)
    (fun idx hk p hp hp2 hc h => h5 idx hk p hp hp2 hc h.2) h7

theorem three_le_degCount_E8_of_three_or_five {p n : ℕ} (hp : p = 3 ∨ p = 5) (hn : ¬ p ∣ n) :
    3 ≤ degCount Tag.E8 (orderOf ((n : ℕ) : ZMod p)) := by
  rcases hp with rfl | rfl
  · rcases orderOf_natCast_zmod_three hn with h | h <;> rw [h] <;> decide
  · rcases orderOf_natCast_zmod_five hn with h | h | h <;> rw [h] <;> decide

theorem three_le_degCount_E7_of_three {n : ℕ} (hn : ¬ 3 ∣ n) :
    3 ≤ degCount Tag.E7 (orderOf ((n : ℕ) : ZMod 3)) := by
  rcases orderOf_natCast_zmod_three hn with h | h <;> rw [h] <;> decide

theorem crossCharInnerAt_E7_of_split
    (h3 : CrossCharInnerAt .E7 fun _ p => p = 3)
    (h5 : CrossCharInnerAt .E7 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5)
    (h7 : CrossCharInnerAt .E7 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p))) ∧ 7 ≤ p) :
    CrossCharInnerAt .E7 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E7 q ∧
      3 ≤ degCount Tag.E7 (orderOf ((q.card : ℕ) : ZMod p)) := by
  refine CrossCharInnerAt.of_split (fun idx hk p hp hp2 hc h => h3 idx hk p hp hp2 hc h.2)
    (fun idx hk p hp hp2 hc ⟨⟨q, hq, hcnt⟩, h5p⟩ => ?_) h7
  subst h5p
  refine h5 idx hk 5 hp hp2 hc ⟨⟨q, hq, ?_⟩, rfl⟩
  have hpq : 5 ≠ q.p := fun h => hc (by rw [hq]; simp [h])
  have hn := not_dvd_card_of_ne hp hpq
  rw [five_dvd_sq_sub_one_iff hn]
  rcases orderOf_natCast_zmod_five hn with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at hcnt
    exact absurd hcnt (by decide)

theorem crossCharInnerAt_E6_of_split
    (h5 : CrossCharInnerAt .E6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5)
    (h7 : CrossCharInnerAt .E6 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) ∧ 7 ≤ p) :
    CrossCharInnerAt .E6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p := by
  refine CrossCharInnerAt.of_split (fun idx hk p hp hp2 hc h => ?_)
    (fun idx hk p hp hp2 hc h => ?_) h7
  · obtain ⟨⟨q, -, -, hp5⟩, h3p⟩ := h
    omega
  · obtain ⟨⟨q, hq, hcnt, -⟩, h5p⟩ := h
    subst h5p
    refine h5 idx hk 5 hp hp2 hc ⟨⟨q, hq, ?_⟩, rfl⟩
    have hpq : 5 ≠ q.p := fun h => hc (by rw [hq]; simp [h])
    have hn := not_dvd_card_of_ne hp hpq
    rw [five_dvd_sq_sub_one_iff hn]
    rcases orderOf_natCast_zmod_five hn with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hcnt
      exact absurd hcnt (by decide)

theorem crossCharInnerAt_twistedE6_of_split
    (h5 : CrossCharInnerAt .twistedE6 fun idx p =>
      (∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧ 5 ∣ q.card ^ 2 - 1) ∧ p = 5)
    (h7 : CrossCharInnerAt .twistedE6 fun idx p => (∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) ∧
        7 ≤ p) :
    CrossCharInnerAt .twistedE6 fun idx p => ∃ q : TauCeti.PrimePower, idx.1 = .twistedE6 q ∧
      3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p := by
  refine CrossCharInnerAt.of_split (fun idx hk p hp hp2 hc h => ?_)
    (fun idx hk p hp hp2 hc h => ?_) h7
  · obtain ⟨⟨q, -, -, hp5⟩, h3p⟩ := h
    omega
  · obtain ⟨⟨q, hq, hcnt, -⟩, h5p⟩ := h
    subst h5p
    refine h5 idx hk 5 hp hp2 hc ⟨⟨q, hq, ?_⟩, rfl⟩
    have hpq : 5 ≠ q.p := fun h => hc (by rw [hq]; simp [h])
    have hn := not_dvd_card_of_ne hp hpq
    rw [five_dvd_sq_sub_one_iff hn]
    rcases orderOf_natCast_zmod_five hn with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hcnt
      exact absurd hcnt (by decide)

end CFSG.HardMathSupport.Timmesfeld.CrossChar
