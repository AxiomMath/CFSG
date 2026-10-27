module

public import CFSG.Certificates.Kernel.KDense.Planes15Sound
public import CFSG.Certificates.Kernel.KDense.SepSpread
public import CFSG.YGroups.Y443.Native.Witness
public import CFSG.Certificates.Kernel.Trace6091.TwinEq

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.KDense.SepAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.KDense.InitAux
  CFSG.KC.KDense.P15 CFSG.KC.KDense.TabAux CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371
  CFSG.YGroups.Y443Native


theorem testBit_shl4 {v : ℕ} (hv : v < 16) (a l i : ℕ) (hi : i < 4) :
    (Nat.shiftLeft v (Nat.mul 4 a)).testBit (4 * l + i) = (decide (l = a) && v.testBit i) := by
  rw [nshl, nmul, Nat.testBit_shiftLeft]
  by_cases h : l = a
  · subst h
    simp [show 4 * l + i - 4 * l = i by omega]
  · rw [decide_eq_false h, Bool.false_and]
    by_cases h2 : 4 * l + i ≥ 4 * a
    · rw [decide_eq_true h2, Bool.true_and]
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le hv (by
        have := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 4 ≤ 4 * l + i - 4 * a)
        simpa using this)
    · rw [decide_eq_false h2, Bool.false_and]

theorem testBit_rec24 {V : ℕ → ℕ} (hV : ∀ k, V k < 16) {N l i : ℕ} (hl : l < N) (hi : i < 4) :
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft (V k) (Nat.mul (nat_lit 4) k))) N).testBit
        (4 * l + i) = (V l).testBit i := by
  rw [Bool.eq_iff_iff, testBit_foldOr]
  simp only [Nat.zero_testBit, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨k, hk, h⟩
    rw [testBit_shl4 (hV k) k l i hi] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1]
    exact h.2
  · intro h
    refine ⟨l, hl, ?_⟩
    rw [testBit_shl4 (hV l) l l i hi]
    simp [h]

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  cases hc : Nat.blt a b
  · rfl
  · have : a < b := by simpa using hc
    omega

theorem brec_t (a b : ℕ) : Bool.rec (motive := fun _ => ℕ) a b true = b := rfl

theorem brec_f (a b : ℕ) : Bool.rec (motive := fun _ => ℕ) a b false = a := rfl

theorem andB_t (b : Bool) : andB true b = b := rfl

theorem land_low {x k : ℕ} : Nat.land x (2 ^ k - 1) = x % 2 ^ k := by
  rw [nland, Nat.and_two_pow_sub_one_eq_mod]

theorem land31 {t i : ℕ} (hi : i < 32) : Nat.land (32 * t + i) (nat_lit 31) = i := by
  have h := land_low (x := 32 * t + i) (k := 5)
  have e : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e] at h
  exact h.trans (by omega)

theorem shr5 {t i : ℕ} (hi : i < 32) : Nat.shiftRight (32 * t + i) (nat_lit 5) = t := by
  have h : Nat.shiftRight (32 * t + i) 5 = (32 * t + i) / 2 ^ 5 := by
    rw [nshr, Nat.shiftRight_eq_div_pow]
  have e : (2 : ℕ) ^ 5 = 32 := by norm_num
  rw [e] at h
  exact h.trans (by omega)

theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]

theorem bitN_dec (x i : ℕ) : Nat.beq (bitN x i) (nat_lit 1) = x.testBit i := by
  rw [P15.bitN_eq']
  cases x.testBit i <;> rfl

theorem wordT_testBit (a k : ℕ) : (wordT a).testBit k = (Native.wordN a).testBit k := by
  rw [CFSG.KC.Trace6091.wordT_eq, native_wordN]

@[expose] def vOdd (w i l : ℕ) : ℕ :=
  if w.testBit l then (if l = i then 3 else 14) else (if l = i then 12 else 1)

theorem vOdd_lt (w i l : ℕ) : vOdd w i l < 16 := by
  unfold vOdd
  split_ifs <;> decide

theorem brec_of {a b : ℕ} {c : Bool} (h : c = true) :
    Bool.rec (motive := fun _ => ℕ) a b c = b := by
  subst h
  rfl

theorem brec_off {a b : ℕ} {c : Bool} (h : c = false) :
    Bool.rec (motive := fun _ => ℕ) a b c = a := by
  subst h
  rfl

@[expose] noncomputable def negF : ℕ → ℕ → ℕ := fun b r => Bool.rec (motive := fun _ => Nat) r
  (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1))

theorem negF_eq (b r : ℕ) : negF b r = Bool.rec (motive := fun _ => Nat) r
    (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1)) := rfl

theorem odd_core {neg : ℕ → ℕ → ℕ} (hneg : negF = neg) {t i N l j : ℕ} (hl : l < N) (hj : j < 4) :
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc => Nat.lor acc (Nat.shiftLeft
      (neg (bitN (wordT (Nat.shiftLeft t (nat_lit 1))) k)
        (Bool.rec (motive := fun _ => ℕ) (nat_lit 1) (nat_lit 12) (Nat.beq k i)))
      (Nat.mul (nat_lit 4) k))) N).testBit (4 * l + j) = (vOdd (wordT (2 * t)) i l).testBit j := by
  subst hneg
  have key : ∀ k, negF (bitN (wordT (Nat.shiftLeft t (nat_lit 1))) k)
      (Bool.rec (motive := fun _ => ℕ) (nat_lit 1) (nat_lit 12) (Nat.beq k i)) =
        vOdd (wordT (2 * t)) i k := by
    intro k
    have e : Nat.shiftLeft t (nat_lit 1) = 2 * t := by
      rw [nshl, Nat.shiftLeft_eq, pow_one, Nat.mul_comm]
    rw [negF_eq, bitN_dec, beq_dec, e]
    unfold vOdd
    cases hw : (wordT (2 * t)).testBit k <;> by_cases hk : k = i <;> simp [hk]
  have hV : ∀ k, negF (bitN (wordT (Nat.shiftLeft t (nat_lit 1))) k)
      (Bool.rec (motive := fun _ => ℕ) (nat_lit 1) (nat_lit 12) (Nat.beq k i)) < 16 := by
    intro k
    rw [key]
    exact vOdd_lt _ _ _
  rw [testBit_rec24 hV hl hj, key]

theorem svRec_odd (OCT : ℕ) {t i : ℕ} (ht : t < 2048) (hi : i < 24) {l j : ℕ} (hl : l < 24)
    (hj : j < 4) :
    (svRec OCT (32 * t + i)).testBit (4 * l + j) = (vOdd (wordT (2 * t)) i l).testBit j := by
  unfold svRec
  generalize hN : nat_lit 24 = N
  generalize hneg : (fun b r => Bool.rec (motive := fun _ => Nat) r
    (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1))) = neg
  have hl' : l < N := by rw [← hN]; exact hl
  have hi' : i < N := by rw [← hN]; exact hi
  have hz1 : Nat.sub (32 * t + i) (nat_lit 114688) = 0 :=
    Nat.sub_eq_zero_of_le (by omega : 32 * t + i ≤ 114688)
  have hz2 : Nat.sub (32 * t + i) (nat_lit 65536) = 0 :=
    Nat.sub_eq_zero_of_le (by omega : 32 * t + i ≤ 65536)
  have hc1 : Nat.blt (32 * t + i) (nat_lit 65536) = true := blt_t (by omega : 32 * t + i < 65536)
  rw [hz1, hz2, shr5 (t := t) (by omega : i < 32), land31 (t := t) (by omega : i < 32)]
  beta_reduce
  rw [brec_of hc1, brec_of (blt_t hi')]
  exact odd_core hneg hl' hj

@[expose] def vOct (w d l : ℕ) : ℕ :=
  if w.testBit l then (if d.testBit l then 13 else 2) else (if d.testBit l then 11 else 0)

theorem vOct_lt (w d l : ℕ) : vOct w d l < 16 := by
  unfold vOct
  split_ifs <;> decide

theorem oct_core {w d N l j : ℕ} (hl : l < N) (hj : j < 4) :
    (Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun k acc => Nat.lor acc (Nat.shiftLeft
      (Nat.mod (Nat.sub (Nat.add (nat_lit 15) (Nat.mul (nat_lit 2) (bitN w k)))
        (Nat.mul (nat_lit 4) (bitN d k))) (nat_lit 15))
      (Nat.mul (nat_lit 4) k))) N).testBit (4 * l + j) = (vOct w d l).testBit j := by
  have key : ∀ k, Nat.mod (Nat.sub (Nat.add (nat_lit 15) (Nat.mul (nat_lit 2) (bitN w k)))
      (Nat.mul (nat_lit 4) (bitN d k))) (nat_lit 15) = vOct w d k := by
    intro k
    rw [P15.bitN_eq', P15.bitN_eq']
    unfold vOct
    cases w.testBit k <;> cases d.testBit k <;> rfl
  have hV : ∀ k, Nat.mod (Nat.sub (Nat.add (nat_lit 15) (Nat.mul (nat_lit 2) (bitN w k)))
      (Nat.mul (nat_lit 4) (bitN d k))) (nat_lit 15) < 16 := fun k => by
    rw [key]
    exact vOct_lt _ _ _
  rw [testBit_rec24 hV hl hj, key]

theorem svRec_oct (OCT : ℕ) {q : ℕ} (hq : q < 48576) {l j : ℕ} (hl : l < 24) (hj : j < 4) :
    (svRec OCT (65536 + q)).testBit (4 * l + j) =
      (vOct (wordT (f12 OCT (Nat.shiftRight q (nat_lit 6))))
        (spreadT (wordT (f12 OCT (Nat.shiftRight q (nat_lit 6))))
          (Nat.add (Nat.shiftLeft (Nat.land q (nat_lit 63)) (nat_lit 1))
            (parT (nat_lit 6) (Nat.land q (nat_lit 63))))) l).testBit j := by
  unfold svRec
  generalize hN : nat_lit 24 = N
  generalize hneg : (fun b r => Bool.rec (motive := fun _ => Nat) r
    (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1))) = neg
  have hl' : l < N := by rw [← hN]; exact hl
  have hz1 : Nat.sub (65536 + q) (nat_lit 114688) = 0 :=
    Nat.sub_eq_zero_of_le (by omega : 65536 + q ≤ 114688)
  have hz2 : Nat.sub (65536 + q) (nat_lit 65536) = q := Nat.add_sub_cancel_left (n := 65536) (m := q)
  have hc1 : Nat.blt (65536 + q) (nat_lit 65536) = false := blt_f (by omega : 65536 ≤ 65536 + q)
  have hc2 : Nat.blt (65536 + q) (nat_lit 114112) = true := blt_t (by omega : 65536 + q < 114112)
  rw [hz1, hz2]
  beta_reduce
  rw [brec_off hc1, brec_of hc2]
  exact oct_core hl' hj

@[expose] def vPair (e a b l : ℕ) : ℕ :=
  if l = a then 4 else if l = b then (if e = 0 then 11 else 4) else 0

theorem shl4' {v : ℕ} (hv : v < 16) (a l i : ℕ) (hi : i < 4) :
    (Nat.shiftLeft v (Nat.mul (nat_lit 4) a)).testBit (4 * l + i) = (decide (l = a) && v.testBit i) :=
  testBit_shl4 hv a l i hi

theorem pair_core {e a b l j : ℕ} (he : e < 2) (hab : a < b) (hj : j < 4) :
    (Nat.lor (Nat.shiftLeft (nat_lit 4) (Nat.mul (nat_lit 4) a))
      (Nat.shiftLeft (Bool.rec (motive := fun _ => ℕ) (nat_lit 4) (nat_lit 11) (Nat.beq e (nat_lit 0)))
        (Nat.mul (nat_lit 4) b))).testBit (4 * l + j) = (vPair e a b l).testBit j := by
  have hs : Bool.rec (motive := fun _ => ℕ) (nat_lit 4) (nat_lit 11) (Nat.beq e (nat_lit 0)) =
      if e = 0 then 11 else 4 := by
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl <;> rfl
  rw [nlor, Nat.testBit_or, shl4' (by decide) _ _ _ hj, hs,
    shl4' (by split <;> decide) _ _ _ hj]
  unfold vPair
  have hne : a ≠ b := Nat.ne_of_lt hab
  by_cases h1 : l = a
  · subst h1
    simp [hne]
  · by_cases h2 : l = b
    · subst h2
      simp [hne.symm]
    · simp [h1, h2]

theorem svRec_pair (OCT : ℕ) {e a b : ℕ} (he : e < 2) (hab : a < b) (hb : b < 24) {l j : ℕ}
    (hj : j < 4) :
    (svRec OCT (114688 + (1024 * e + (32 * a + b)))).testBit (4 * l + j) =
      (vPair e a b l).testBit j := by
  unfold svRec
  generalize hN : nat_lit 24 = N
  generalize hneg : (fun b r => Bool.rec (motive := fun _ => Nat) r
    (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1))) = neg
  have hb' : b < N := by rw [← hN]; exact hb
  have hpp : Nat.sub (114688 + (1024 * e + (32 * a + b))) (nat_lit 114688) =
      32 * (32 * e + a) + b := by
    have : 114688 + (1024 * e + (32 * a + b)) - 114688 = 32 * (32 * e + a) + b := by omega
    exact this
  have h1 : Nat.land (Nat.shiftRight (32 * (32 * e + a) + b) (nat_lit 5)) (nat_lit 31) = a := by
    rw [shr5 (t := 32 * e + a) (i := b) (by omega)]
    have := land31 (t := e) (i := a) (by omega)
    exact this
  have h2 : bitN (32 * (32 * e + a) + b) (nat_lit 10) = e := by
    rw [P15.bitN_eq', Nat.toNat_testBit]
    have e1 : (2 : ℕ) ^ 10 = 1024 := by norm_num
    rw [e1]
    omega
  have hc1 : Nat.blt (114688 + (1024 * e + (32 * a + b))) (nat_lit 65536) = false :=
    blt_f (by omega : 65536 ≤ 114688 + (1024 * e + (32 * a + b)))
  have hc2 : Nat.blt (114688 + (1024 * e + (32 * a + b))) (nat_lit 114112) = false :=
    blt_f (by omega : 114112 ≤ 114688 + (1024 * e + (32 * a + b)))
  have hp1 : Nat.blt (32 * (32 * e + a) + b) (nat_lit 2048) = true :=
    blt_t (by omega : 32 * (32 * e + a) + b < 2048)
  rw [hpp]
  beta_reduce
  rw [brec_off hc1, brec_off hc2]
  rw [h1, land31 (t := 32 * e + a) (i := b) (by omega), h2, hp1]
  rw [blt_t hab, blt_t hb', andB_t, andB_t, brec_t (nat_lit 0)]
  exact pair_core he hab hj

theorem wordT_eqN (a : ℕ) : wordT a = Native.wordN a := by
  rw [CFSG.KC.Trace6091.wordT_eq, native_wordN]

theorem svRec_entry {OCT : ℕ} (h1 : octOK OCT = true) {q : ℕ}
    (hq : q < 98280) {l : ℕ} (hl : l < 24) :
    ∃ v : ℕ, v < 16 ∧ (∀ i < 4, (svRec OCT (xposK q)).testBit (4 * l + i) = v.testBit i) ∧
      (v : ZMod 15) = (((shortVecN q)[l]! : ℤ) : ZMod 15) := by
  have hk : ((⟨l, hl⟩ : Fin 24) : ℕ) = l := rfl
  rcases Nat.lt_or_ge q 552 with hq1 | hq1
  ·
    obtain ⟨hab, hb⟩ := pairTab_ok (q / 2) (by omega)
    have hx : xposK q = 114688 + (1024 * (q % 2) + (32 * (Native.pairTab ())[q / 2]!.1 +
        (Native.pairTab ())[q / 2]!.2)) := by
      unfold xposK
      rw [ite_eq_left hq1]
      split_ifs <;> omega
    refine ⟨vPair (q % 2) (Native.pairTab ())[q / 2]!.1 (Native.pairTab ())[q / 2]!.2 l, ?_,
      fun i hi => ?_, ?_⟩
    · unfold vPair
      split_ifs <;> decide
    · rw [hx]
      exact svRec_pair OCT (Nat.mod_lt _ (by decide)) hab hb hi
    · have := CFSG.YGroups.Y443.shortVecN_F1 q hq1 ⟨l, hl⟩
      rw [hk] at this
      rw [this]
      unfold vPair
      have hne : (Native.pairTab ())[q / 2]!.1 ≠ (Native.pairTab ())[q / 2]!.2 := Nat.ne_of_lt hab
      by_cases e1 : l = (Native.pairTab ())[q / 2]!.1
      · have e2 : ¬ l = (Native.pairTab ())[q / 2]!.2 := by rw [e1]; exact hne
        rw [ite_eq_left e1, ite_eq_left e1, ite_eq_right e2]
        decide
      · by_cases e2 : l = (Native.pairTab ())[q / 2]!.2
        · rw [ite_eq_right e1, ite_eq_left e2, ite_eq_right e1, ite_eq_left e2]
          rcases Nat.mod_two_eq_zero_or_one q with h0 | h0
          · rw [ite_eq_left h0, ite_eq_left h0]
            decide
          · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
            decide
        · rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e1, ite_eq_right e2]
          decide
  rcases Nat.lt_or_ge q 49704 with hq2 | hq2
  ·
    have hx : xposK q = 32 * ((q - 552) / 24) + (q - 552) % 24 := by
      unfold xposK
      rw [ite_eq_right (by omega), ite_eq_left hq2]
    refine ⟨vOdd (wordT (2 * ((q - 552) / 24))) ((q - 552) % 24) l, vOdd_lt _ _ _,
      fun i hi => ?_, ?_⟩
    · rw [hx]
      exact svRec_odd OCT (by omega) (Nat.mod_lt _ (by decide)) hl hi
    · have := CFSG.YGroups.Y443.shortVecN_F2 q hq1 hq2 ⟨l, hl⟩
      rw [hk] at this
      rw [this]
      unfold vOdd
      rw [wordT_eqN]
      cases (Native.wordN (2 * ((q - 552) / 24))).testBit l <;>
        by_cases e : l = (q - 552) % 24 <;> simp [e] <;> decide
  ·
    have hq' : q - 49704 < 48576 := by omega
    have hx : xposK q = 65536 + (q - 49704) := by
      unfold xposK
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    have ho : (q - 49704) / 64 < 759 := by omega
    have e1 : Nat.shiftRight (q - 49704) (nat_lit 6) = (q - 49704) / 64 := by
      rw [nshr, Nat.shiftRight_eq_div_pow]
    have e2 : Nat.land (q - 49704) (nat_lit 63) = (q - 49704) % 64 := by
      have h := land_low (x := q - 49704) (k := 6)
      exact h
    have e3 : Nat.add (Nat.shiftLeft ((q - 49704) % 64) (nat_lit 1))
        (parT (nat_lit 6) ((q - 49704) % 64)) = (Native.evenTab ())[(q - 49704) % 64]! := by
      rw [evenTab_eq _ (Nat.mod_lt _ (by decide)), nadd, nshl, Nat.shiftLeft_eq, pow_one,
        Nat.mul_comm]
    have eW : wordT (f12 OCT (Nat.shiftRight (q - 49704) (nat_lit 6))) =
        Native.wordN (Native.octTab ())[(q - 49704) / 64]! := by
      rw [e1, f12_octOK h1 ho, wordT_eqN]
    have hpop := (Native.octTab_spec _ ho).2
    have hw8 : (flt (fun i => (Native.wordN (Native.octTab ())[(q - 49704) / 64]!).testBit i)
        24).length = 8 := by
      rw [flt_length_popcN]
      exact hpop
    refine ⟨vOct (wordT (f12 OCT (Nat.shiftRight (q - 49704) (nat_lit 6))))
        (spreadT (wordT (f12 OCT (Nat.shiftRight (q - 49704) (nat_lit 6))))
          (Nat.add (Nat.shiftLeft (Nat.land (q - 49704) (nat_lit 63)) (nat_lit 1))
            (parT (nat_lit 6) (Nat.land (q - 49704) (nat_lit 63))))) l, vOct_lt _ _ _,
      fun i hi => ?_, ?_⟩
    · rw [hx]
      exact svRec_oct OCT hq' hl hi
    · have := CFSG.YGroups.Y443.shortVecN_F3 q hq2 ⟨l, hl⟩
      rw [hk] at this
      rw [this, e2, e3, eW, spreadT_eq hw8]
      unfold vOct
      cases (Native.wordN (Native.octTab ())[(q - 49704) / 64]!).testBit l <;>
        cases (Native.spreadG (Native.wordN (Native.octTab ())[(q - 49704) / 64]!)
          (Native.evenTab ())[(q - 49704) % 64]!).testBit l <;> simp <;> decide

end CFSG.KC.KDense.SepAux

end
