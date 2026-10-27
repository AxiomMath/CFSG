module

public import Certificates.Data.Kernel.Sp43KList
public import CFSG.Certificates.Kernel.Sp43KSound

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43

theorem okT_spec {c : ℕ} (h : okT c = true) : ExT c ∧ c < 2 ^ 32 := by
  simp only [okT, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun n hn => ?_, ?_⟩
  · have := congrArg (fun x => x.testBit n) h1
    simp only [Nat.testBit_and, testBit_laneT hn, Bool.and_true, Nat.zero_testBit,
      testBit_high] at this
    simpa [Nat.add_comm] using this
  · rw [Nat.shiftRight_eq_div_pow] at h2
    exact (Nat.div_eq_zero_iff_lt (by positivity)).1 h2

private theorem bits_of_val {b1 b2 b1' b2' : Bool} (h : (b1 && b2) = false)
    (h' : (b1' && b2') = false)
    (e : (if b1 then (1 : ZMod 3) else if b2 then 2 else 0) =
      if b1' then (1 : ZMod 3) else if b2' then 2 else 0) : b1 = b1' ∧ b2 = b2' := by
  revert h h' e
  decide +revert

private theorem exists_ix {m : ℕ} (hm : m < 4) : ∃ x, ix x = m := by
  interval_cases m
  exacts [⟨.inl 0, rfl⟩, ⟨.inl 1, rfl⟩, ⟨.inr 0, rfl⟩, ⟨.inr 1, rfl⟩]

theorem toMT_inj {c c' : ℕ} (hc : okT c = true) (hc' : okT c' = true) (h : toMT c = toMT c') :
    c = c' := by
  obtain ⟨ec, lc⟩ := okT_spec hc
  obtain ⟨ec', lc'⟩ := okT_spec hc'
  have hk : ∀ k < 16, c.testBit k = c'.testBit k ∧ c.testBit (k + 16) = c'.testBit (k + 16) := by
    intro k hk
    obtain ⟨x, hx⟩ := exists_ix (m := k / 4) (by omega)
    obtain ⟨y, hy⟩ := exists_ix (m := k % 4) (by omega)
    have e := congrFun (congrFun h x) y
    simp only [toMT, val2, hx, hy, testBit_high] at e
    have hkk : 4 * (k / 4) + k % 4 = k := by omega
    rw [hkk] at e
    exact bits_of_val (ec k hk) (ec' k hk) e
  apply Nat.eq_of_testBit_eq
  intro k
  rcases lt_or_ge k 16 with h1 | h1
  · exact (hk k h1).1
  rcases lt_or_ge k 32 with h2 | h2
  · have := (hk (k - 16) (by omega)).2
    rwa [Nat.sub_add_cancel h1] at this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le lc (Nat.pow_le_pow_right (by norm_num) h2)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le lc' (Nat.pow_le_pow_right (by norm_num) h2))]

theorem lstGo_spec {a b n P D e : ℕ} :
    ∀ (R : List (ℕ × ℕ × ℕ × ℕ)) (s : ℕ), lstGo a b n P D e R s = true →
      e = s + R.length ∧ ∀ i, s ≤ i → i < e →
        i < n ∧ lstOne a b n P D i (R.getD (i - s) (0, 0, 0, 0)) = true
  | [], s, h => by
    have h' : (s == e) = true := h
    have hse : s = e := beq_iff_eq.1 h'
    exact ⟨by simp [hse], fun i hi hie => by omega⟩
  | r :: R, s, h => by
    have h' : (Nat.blt s n && lstOne a b n P D s r && lstGo a b n P D e R (s + 1)) = true := h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h'
    obtain ⟨⟨hsn, hone⟩, hrest⟩ := h'
    obtain ⟨he, hall⟩ := lstGo_spec R (s + 1) hrest
    refine ⟨by simp [he]; omega, fun i hi hie => ?_⟩
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact ⟨hsn, by simpa using hone⟩
    · obtain ⟨h1, h2⟩ := hall i hlt hie
      refine ⟨h1, ?_⟩
      have : i - s = (i - (s + 1)) + 1 := by omega
      rw [this, List.getD_cons_succ]
      exact h2

end CFSG.KC.Sp43K

end
