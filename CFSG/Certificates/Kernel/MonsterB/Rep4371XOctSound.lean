module

public import Certificates.Data.Kernel.MonsterB.Rep4371XOct
public import CFSG.Certificates.Kernel.MonsterB.Rep4371XRaw
public import CFSG.Certificates.Kernel.Trace6091.Tabs

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Trace6091 CFSG.KC.Rep4371Row CFSG.Monster.B

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem spread_bit (w m y : Nat) : (spreadT w m).testBit y =
    (decide (y < 24) && w.testBit y && m.testBit (TabAux.flt (fun i => w.testBit i) y).length) := by
  rw [TabAux.spreadT_eq']
  exact (TabAux.spST_spec w m 24).2 y

theorem spread_and (w m m' : Nat) : spreadT w (m &&& m') = spreadT w m &&& spreadT w m' := by
  apply Nat.eq_of_testBit_eq
  intro y
  rw [Nat.testBit_and, spread_bit, spread_bit, spread_bit, Nat.testBit_and]
  cases decide (y < 24) <;> cases w.testBit y <;> simp

theorem spread_lt (w m : Nat) : spreadT w m < 16777216 := by
  have h : spreadT w m < 2 ^ 24 := by
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [spread_bit, decide_eq_false (by omega)]
    rfl
  exact h

theorem spread_inj {w : Nat} (hl : (TabAux.flt (fun i => w.testBit i) 24).length = 8) {m m' : Nat}
    (hm : m < 256) (hm' : m' < 256) (h : spreadT w m = spreadT w m') : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 8
  · obtain ⟨hy1, hy2, hy3⟩ := TabAux.flt_get (fun i => w.testBit i) 24 t (by rw [hl]; exact ht)
    have e : (spreadT w m).testBit (TabAux.flt (fun i => w.testBit i) 24)[t] =
        (spreadT w m').testBit (TabAux.flt (fun i => w.testBit i) 24)[t] := by rw [h]
    rw [spread_bit, spread_bit, hy3, decide_eq_true hy1, hy2] at e
    simpa using e
  · have h8 : (256 : Nat) ≤ 2 ^ t := by
      have := Nat.pow_le_pow_right (n := 2) (by decide) (show 8 ≤ t by omega)
      exact this
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm h8), Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm' h8)]

theorem octDataOK_of (h : octChk = true) : Model.octDataOK = true := by
  unfold Model.octDataOK
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨by rw [octCoeffs_eq]; simp, fun b hb => ?_⟩
  have hb' := List.mem_range.1 hb
  rw [octCoeffs_get hb']
  have hc := allBelow_spec h (by decide) b hb'
  simp only [strictB_eq, wordT_eq] at hc
  obtain ⟨hw, h3⟩ := octT_word hb'
  have h0 : (Model.wordN (octT b)).testBit 0 = true := by
    rw [Nat.testBit_zero]
    simp
    omega
  have h1 : (Model.wordN (octT b)).testBit 1 = true := by
    rw [Nat.testBit_succ, Nat.testBit_zero]
    simp
    omega
  have hl : (TabAux.flt (fun i => (Model.wordN (octT b)).testBit i) 24).length = 8 := by
    rw [TabAux.flt_length_popcN]
    exact hw
  have hsp : ∀ m, Model.spreadN (Model.wordN (octT b)) m = spreadT (Model.wordN (octT b)) m := fun m => by
    rw [spreadN_eq h0 h1, TabAux.spreadT_eq hl]
  generalize Model.wordN (octT b) = w at hc hl hsp
  dsimp only
  simp only [hsp]
  rw [List.all_eq_true]
  intro m hm
  have hm' := List.mem_range.1 hm
  have hcm := allBelow_spec hc (by decide) m hm'
  simp only [octM, strictB_eq] at hcm
  obtain ⟨c1, hcm⟩ := bAnd_true hcm
  obtain ⟨c2, c3⟩ := bAnd_true hcm
  have e1 := Nat.eq_of_beq_eq_true c1
  have e2 := Nat.eq_of_beq_eq_true c2
  have e3 := Nat.eq_of_beq_eq_true c3
  rw [KeysOKAux.popc24_eq, Rep4371.native_popcN, popcT_eq] at e2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨e1, e2⟩, e3⟩, fun m' hm'' => ⟨spread_and w m m', ?_⟩⟩
  rw [Nat.mod_eq_of_lt (spread_lt w m), Nat.mod_eq_of_lt (spread_lt w m')]
  by_cases hmm : m = m'
  · simp [hmm]
  · have hne : spreadT w m ≠ spreadT w m' := fun e => hmm (spread_inj hl hm' hm'' e)
    simp [hmm, hne]

end CFSG.KC.Rep4371X

end
