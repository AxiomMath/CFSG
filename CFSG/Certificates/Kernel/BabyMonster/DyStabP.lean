module

public import CFSG.Certificates.Kernel.BabyMonster.DyStab

public section

namespace CFSG.KC.BM.Dy

open CFSG.KC.BM CFSG.KC.BM.Lat CFSG.KC.YModel CFSG.KC.BM.Pkt

@[expose] def skipP (k : Nat) : Nat := if k < 1197 then k else k + 1

@[expose] noncomputable def stPOK (Bs : List (List Nat)) (F : Nat → Nat) (f : Nat) (R : Nat → Nat)
    (s : Nat) : Bool :=
  Nat.beq (projRow (nat_lit 1197) f (dyElim (nat_lit 256) Bs (nat_lit 0) (F (skipP s)))) (R s)

theorem stPOK_of {Bs : List (List Nat)} {F : Nat → Nat} {f : Nat} {R : Nat → Nat} {s V W : Nat}
    (h : Nat.beq (projRow (nat_lit 1197) f (dyElim (nat_lit 256) Bs (nat_lit 0) V)) W = true)
    (hV : V = F (skipP s)) (hW : W = R s) : stPOK Bs F f R s = true := by
  subst hV hW
  exact h

@[expose] def RowStabP (Bs : List (List Nat)) (N : ℕ → ℕ → ℤ) (f r i : ℕ) : Prop :=
  ∃ q : ℕ → ℤ, (∀ t < 4370, (q (skipP t) + q 1197 * (if f.testBit (skipP t) then 1 else 0)) % 2 =
      if r.testBit t then 1 else 0) ∧
    ∀ u < 4371, ∃ w : ℤ, ∑ t ∈ Finset.range 4371, (ent Bs i t : ℤ) * N t u =
      8 * (∑ j ∈ Finset.range 4371, q j * (ent Bs j u : ℤ) + 256 * w)

theorem projRow_testBit (p f r t : Nat) :
    (projRow p f r).testBit t = (r.testBit (if t < p then t else t + 1) ^^
      (r.testBit p && f.testBit (if t < p then t else t + 1))) := by
  have hb : Nat.land (Nat.shiftRight r p) (nat_lit 1) = if r.testBit p then 1 else 0 := by
    change (r >>> p) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    split <;> rename_i h <;> simp at h <;> omega
  have hy : ∀ k, (r ^^^ ((if r.testBit p then 1 else 0) * f)).testBit k =
      (r.testBit k ^^ (r.testBit p && f.testBit k)) := fun k => by
    cases r.testBit p <;> simp
  unfold projRow
  simp only
  rw [hb]
  change (((r ^^^ ((if r.testBit p then 1 else 0) * f)) &&& (1 <<< p - 1)) |||
    ((r ^^^ ((if r.testBit p then 1 else 0) * f)) >>> (p + 1) <<< p)).testBit t = _
  rw [Nat.testBit_or, Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hy, hy]
  by_cases ht : t < p
  · rw [ite_eq_left ht, decide_eq_true ht, decide_eq_false (by omega)]
    simp
  · rw [ite_eq_right ht, decide_eq_false ht, decide_eq_true (by omega),
      show p + 1 + (t - p) = t + 1 by omega]
    simp

theorem parity_xor (a b : ℕ) (c : Bool) :
    ((a : ℤ) + (b : ℤ) * (if c = true then 1 else 0)) % 2 =
      if (decide (a % 2 = 1) ^^ (decide (b % 2 = 1) && c)) = true then 1 else 0 := by
  cases c <;> rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> simp [h1, h2] <;> omega

theorem stMonoP_sound {Bs : List (List Nat)} {Ms : List Nat} {T NM f : Nat} {R : Nat → Nat}
    (hB : blocksOK Bs = true)
    (hr : ∀ j < 4371, dyRowOK (nat_lit 4371) j (recOf Bs j) = true)
    (hs : shifts16 dyDs = true) (hal : allAligned Ms = true) (hn : netOK Ms T NM = true)
    (hv : netV Ms T = true) {s : Nat} (hsl : s < 4370) (h : stPOK Bs (monoF Bs Ms NM) f R s = true)
    (hR : R s < 2 ^ 4370) :
    RowStabP Bs (kNumMono T) f (R s) (skipP s) := by
  have hsk : skipP s < 4371 := by
    unfold skipP
    split <;> omega
  have hRi : projRow 1197 f (dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM (skipP s))) = R s :=
    Nat.eq_of_beq_eq_true h
  have hne : dyElim (2 ^ 8) Bs 0 (monoF Bs Ms NM (skipP s)) ≠ dyFail := by
    intro e
    rw [e] at hRi
    have h1 : (R s).testBit 4999 = false := by
      have e : (R s).testBit 4999 = (R s >>> 4370).testBit 629 := by rw [Nat.testBit_shiftRight]
      rw [e, Nat.shiftRight_eq_zero _ _ hR, Nat.zero_testBit]
    have hd1 : dyFail.testBit 1197 = false := by
      change (1 <<< 5000).testBit 1197 = false
      rw [Nat.testBit_shiftLeft]
      decide
    have hd2 : dyFail.testBit (4999 + 1) = true := by
      change (1 <<< 5000).testBit (4999 + 1) = true
      rw [Nat.testBit_shiftLeft]
      decide
    rw [← hRi, projRow_testBit, ite_eq_right (show ¬ (4999 < 1197) by decide), hd1, hd2] at h1
    simp at h1
  obtain ⟨Q, hQo, hrow⟩ := mono_row hB hr hs hal hn hv hsk hne
  refine ⟨fun j => (Q j : ℤ), fun t _ => ?_, hrow⟩
  simp only
  have e : (if t < 1197 then t else t + 1) = skipP t := rfl
  rw [← hRi, projRow_testBit, e, hQo, hQo]
  exact parity_xor _ _ _

end CFSG.KC.BM.Dy

end
