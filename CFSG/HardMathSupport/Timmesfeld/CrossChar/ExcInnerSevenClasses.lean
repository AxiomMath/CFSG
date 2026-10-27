module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerOne
public import CFSG.LieType.SeitzGeneration.ExcTorusRankTw
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge
  CFSG.HardMathSupport.Timmesfeld.LocalTwo

theorem degCount_E8_ge_three {e : ℕ} (h : 3 ≤ degCount Tag.E8 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (by simp) (e := e) (by omega)
  have key : ∀ e ≤ 30, 3 ≤ degCount Tag.E8 e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 6 := by
    decide
  exact key e h30 h

theorem degCount_E7_ge_three {e : ℕ} (h : 3 ≤ degCount Tag.E7 e) :
    e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (by simp) (e := e) (by omega)
  have key : ∀ e ≤ 30, 3 ≤ degCount Tag.E7 e → e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 6 := by
    decide
  exact key e h30 h

theorem degCount_E6_ge_three {e : ℕ} (h : 3 ≤ degCount Tag.E6 e) : e = 1 ∨ e = 2 ∨ e = 3 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (e := e) (by omega)
  have key : ∀ e ≤ 30, 3 ≤ degCount Tag.E6 e → e = 1 ∨ e = 2 ∨ e = 3 := by decide
  exact key e h30 h

theorem degCountTw_ge_three {e : ℕ} (h : 3 ≤ degCountTw e) : e = 1 ∨ e = 2 ∨ e = 6 := by
  have h60 := le_sixty_of_degCountTw_pos (e := e) (by omega)
  have key : ∀ e ≤ 60, 3 ≤ degCountTw e → e = 1 ∨ e = 2 ∨ e = 6 := by decide
  exact key e h60 h

theorem dvd_add_one_of_orderOf_eq_two {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 2) : p ∣ q + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : ((q : ℕ) : ZMod p) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have h1 : ((q : ℕ) : ZMod p) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at h
    norm_num at h
  have hm : (((q : ℕ) : ZMod p) - 1) * (((q : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.1 hm with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) h1
  · rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one]
    exact h3

theorem eleven_le_of_prime_seven_le_ne {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h : p ≠ 7) :
    11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

section Conversion

theorem isInnerLocallyBalanced_of_innerPlaneBalanceAtP {k : LieFamily} {e : ℕ} {R : ℕ → Prop}
    (h : InnerPlaneBalanceAtP k e R) (q : TauCeti.PrimePower) (hv : (excIndex k q).Valid)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hR : R p) (hpq : p ≠ q.p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = e) :
    IsInnerLocallyBalanced p (Cat ⟨excIndex k q, hv⟩) :=
  isInnerLocallyBalanced_of_innerPlanes hp (h q hv p hp hp7 hR hpq he)

end Conversion

section Residuals

theorem crossCharInnerAt_E6_seven_of_classes (h2 : InnerPlaneBalanceAt .E6 2)
    (h3 : InnerPlaneBalanceAt .E6 3) :
    CrossCharInnerAt .E6 fun idx p => (∃ q : TauCeti.PrimePower, idx.1 = .E6 q ∧
      3 ≤ degCount Tag.E6 (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) ∧ 7 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨⟨q, hq, hdeg, -⟩, hp7⟩
  change d = _ at hq
  subst hq
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  have hq1 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.2 (TauCeti.PrimePower.card_def q ▸
    pow_ne_zero _ q.prime_p.ne_zero)
  rcases degCount_E6_ge_three hdeg with he | he | he
  · exact crossCharInnerAt_E6_dvd_sub_one _ ⟨q, rfl⟩ p hp hp2 hc
      ⟨q, rfl, hp7, dvd_sub_one_of_orderOf_eq_one hq1 he⟩
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E6)
      (h2.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .E6)
      (h3.atP fun _ => True) q hv hp hp7 trivial hpq he

end Residuals

theorem crossCharInnerAt_twistedE6_seven_of_classes (h1 : InnerPlaneBalanceAt .twistedE6 1)
    (h2 : InnerPlaneBalanceAt .twistedE6 2) (h6 : InnerPlaneBalanceAt .twistedE6 6) :
    CrossCharInnerAt .twistedE6 fun idx p => (∃ q : TauCeti.PrimePower,
      idx.1 = .twistedE6 q ∧ 3 ≤ degCountTw (orderOf ((q.card : ℕ) : ZMod p)) ∧ 5 ≤ p) ∧
        7 ≤ p := by
  rintro ⟨d, hv⟩ hk p hp hp2 hc ⟨⟨q, hq, hdeg, -⟩, hp7⟩
  change d = _ at hq
  subst hq
  have hpq : p ≠ q.p := fun h => hc (by simp [h])
  rcases degCountTw_ge_three hdeg with he | he | he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .twistedE6)
      (h1.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .twistedE6)
      (h2.atP fun _ => True) q hv hp hp7 trivial hpq he
  · exact isInnerLocallyBalanced_of_innerPlaneBalanceAtP (k := .twistedE6)
      (h6.atP fun _ => True) q hv hp hp7 trivial hpq he

end CFSG.HardMathSupport.Timmesfeld.CrossChar
