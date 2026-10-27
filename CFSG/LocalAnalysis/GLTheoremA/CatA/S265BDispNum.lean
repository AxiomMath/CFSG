module

public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem eq_zero_of_two_pow {m : ℕ} (h : 2 ^ (2 * m + 1) = 2) : m = 0 := by
  have h1 : 2 * m + 1 = 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using h)
  omega

theorem cases_of_eleven {e : TauCeti.LieTypeIndex} (he : e.Valid) (hc : e.characteristic = 2)
    (hf : KD264Lie.fieldSize e = 2) (h11 : 11 ∣ lieOrderFormula e)
    (hlt : 13685760 < lieOrderFormula e) :
    (∃ n q, e = .A n q ∧ q.card = 2 ∧ 9 ≤ n) ∨
      (∃ n q, e = .twistedA n q ∧ q.card = 2 ∧ 5 ≤ n) ∨
      (∃ n q, e = .B n q ∧ q.card = 2 ∧ 5 ≤ n) ∨
      (∃ n q, e = .D n q ∧ q.card = 2 ∧ 6 ≤ n) ∨
      (∃ n q, e = .twistedD n q ∧ q.card = 2 ∧ 5 ≤ n) ∨
      (∃ q, e = .E7 q ∧ q.card = 2) ∨ (∃ q, e = .E8 q ∧ q.card = 2) ∨
      (∃ q, e = .twistedE6 q ∧ q.card = 2) := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    have hq : q.card = 2 := hf
    refine Or.inl ⟨n, q, rfl, hq, ?_⟩
    rw [show lieOrderFormula (.A n q) = orderA n q.card from rfl, hq] at h11
    by_contra hn
    push Not at hn
    interval_cases n <;> exact absurd h11 (by decide +kernel)
  | twistedA n q =>
    have hq : q.card = 2 := hf
    refine Or.inr (Or.inl ⟨n, q, rfl, hq, ?_⟩)
    rw [show lieOrderFormula (.twistedA n q) = orderTwistedA n q.card from rfl, hq] at h11 hlt
    by_contra hn
    rcases (show n ≤ 3 ∨ n = 4 by omega) with hn3 | rfl
    · interval_cases n <;> exact absurd h11 (by decide +kernel)
    · exact absurd hlt (by decide +kernel)
  | B n q =>
    have hq : q.card = 2 := hf
    refine Or.inr (Or.inr (Or.inl ⟨n, q, rfl, hq, ?_⟩))
    rw [show lieOrderFormula (.B n q) = orderBC n q.card from rfl, hq] at h11
    by_contra hn
    push Not at hn
    interval_cases n <;> exact absurd h11 (by decide +kernel)
  | C _ _ => exact absurd (by simpa using hc) hs.2
  | D n q =>
    have hq : q.card = 2 := hf
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, q, rfl, hq, ?_⟩)))
    rw [show lieOrderFormula (.D n q) = orderD n q.card from rfl, hq] at h11
    have h4 : 4 ≤ n := hs
    by_contra hn
    rcases (show n = 4 ∨ n = 5 by omega) with rfl | rfl <;>
      exact absurd h11 (by decide +kernel)
  | twistedD n q =>
    have hq : q.card = 2 := hf
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, q, rfl, hq, ?_⟩))))
    rw [show lieOrderFormula (.twistedD n q) = orderTwistedD n q.card from rfl, hq] at h11
    have h4 : 4 ≤ n := hs
    by_contra hn
    obtain rfl : n = 4 := by omega
    exact absurd h11 (by decide +kernel)
  | E6 q =>
    have hq : q.card = 2 := hf
    rw [show lieOrderFormula (.E6 q) = orderE6 q.card from rfl, hq] at h11
    exact absurd h11 (by decide +kernel)
  | E7 q => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hf⟩)))))
  | E8 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hf⟩))))))
  | F4 q =>
    have hq : q.card = 2 := hf
    rw [show lieOrderFormula (.F4 q) = orderF4 q.card from rfl, hq] at h11
    exact absurd h11 (by decide +kernel)
  | G2 q =>
    have hq : q.card = 2 := hf
    exact absurd (show 3 ≤ q.card from hs) (by rw [hq]; norm_num)
  | twistedE6 q =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl, hf⟩))))))
  | trialityD4 q =>
    have hq : q.card = 2 := hf
    rw [show lieOrderFormula (.trialityD4 q) = orderTrialityD4 q.card from rfl, hq] at h11
    exact absurd h11 (by decide +kernel)
  | suzuki m => exact absurd (show 1 ≤ m from hs) (by rw [eq_zero_of_two_pow hf]; norm_num)
  | reeG2 _ => simp at hc
  | reeF4 m => exact absurd (show 1 ≤ m from hs) (by rw [eq_zero_of_two_pow hf]; norm_num)
  | tits => exact absurd h11 (by decide +kernel)

end CFSG.LocalAnalysis.GLTheoremA.S265

end
