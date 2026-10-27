module

public import Certificates.Data.Kernel.Fi22Twist.Leaf
public import CFSG.Certificates.Kernel.Fi22Twist.BfSound
public import CFSG.Certificates.Kernel.Fi22Twist.LvOrbSound
import CFSG.Certificates.Kernel.Spor.Loops

public section

set_option maxRecDepth 400000

namespace CFSG.KC.Fi22Twist

open CFSG.KC.Enum

@[expose] noncomputable def wAp (S : Nat → Nat) (l : List Nat) (x : Nat) : Nat :=
  l.foldr (fun g y => ap (S g) y) x

theorem wAp_nil (S : Nat → Nat) (x : Nat) : wAp S [] x = x := rfl

theorem wAp_cons (S : Nat → Nat) (g : Nat) (l : List Nat) (x : Nat) :
    wAp S (g :: l) x = ap (S g) (wAp S l x) := rfl

theorem wAp_append (S : Nat → Nat) (l l' : List Nat) (x : Nat) :
    wAp S (l ++ l') x = wAp S l (wAp S l' x) := by
  unfold wAp
  rw [List.foldr_append]

theorem recB_tt (e t : Bool) : Bool.rec (motive := fun _ => Bool) e t true = t := rfl

theorem recB_ff (e t : Bool) : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem recN_tt (e t : Nat) : Bool.rec (motive := fun _ => Nat) e t true = t := rfl

theorem recN_ff (e t : Nat) : Bool.rec (motive := fun _ => Nat) e t false = e := rfl

theorem beq_ff {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem blt_ff {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · have := Nat.le_of_ble_eq_true e
    omega

theorem blt_tt {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.ble_eq_true_of_le h

theorem not_tt {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b
  · rfl
  · exact absurd h Bool.false_ne_true

theorem beq_tt {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  rw [h]
  exact Nat.beq_refl b

theorem beq00 : Nat.beq 0 0 = true := rfl

theorem blt88 : Nat.blt 8 8 = false := rfl

theorem sub88 : Nat.sub 8 8 = 0 := rfl

theorem wf4_sound {WF OF BF S : Nat → Nat} (h : ∀ u < 8, wfK WF OF BF S u = true) :
    ∀ u < 8, ∃ l : List Nat, (∀ g ∈ l, g < 19) ∧ (∀ m < 4, wAp S l (bp m) = bp m) ∧
      wAp S l (ap (OF 4) 0) = ap (OF 4) u ∧
      fld(WF u, 24, 4095) = wAp S l (ap (OF 5) 0) ∧
      fld(WF u, 36, 4095) = wAp S l (ap (OF 5) 1) := by
  intro u
  induction u using Nat.strongRecOn with
  | ind u ih =>
    intro hu
    have hc := h u hu
    unfold wfK at hc
    simp only [strictB_eq] at hc
    simp only [blt_tt hu, recB_tt] at hc
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · simp only [beq00, recB_tt] at hc
      obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      exact ⟨[], (fun _ hg => nomatch hg), fun _ _ => rfl, rfl,
        Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩
    simp only [beq_ff (Nat.pos_iff_ne_zero.1 hpos), recB_ff] at hc
    obtain ⟨h1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h2, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h3, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h4, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h5, h6⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    have hpar : fld(WF u, 0, 4095) < u := Nat.le_of_ble_eq_true h1
    have hg : fld(WF u, 12, 4095) < 19 := Nat.le_of_ble_eq_true h2
    obtain ⟨l, hl, hfix, h0, hw0, hw1⟩ := ih _ hpar (by omega)
    refine ⟨fld(WF u, 12, 4095) :: l, fun g hm => ?_, fun m hm => ?_, ?_, ?_, ?_⟩
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hg
      · exact hl g hm
    · rw [wAp_cons, hfix m hm]
      exact fixB_spec h3 m hm
    · rw [wAp_cons, h0]
      exact Nat.eq_of_beq_eq_true h4
    · rw [wAp_cons, ← hw0]
      exact Nat.eq_of_beq_eq_true h5
    · rw [wAp_cons, ← hw1]
      exact Nat.eq_of_beq_eq_true h6

theorem wfB_sound {WF OF BF S : Nat → Nat} (hw : ∀ k < 720, wfK WF OF BF S (8 + k) = true)
    (hb : ∀ k < 720, bfK BF S k = true) :
    ∀ k < 720, ∃ l : List Nat, (∀ g ∈ l, g < 19) ∧ (∀ m < 3, wAp S l (bp m) = bp m) ∧
      (∀ p < 9, fld(BF k, Nat.mul 12 p, 4095) = wAp S l (fld(BF 0, Nat.mul 12 p, 4095))) ∧
      ∀ f < 16, fld(WF (8 + k), Nat.mul 12 f, 4095) = wAp S l (fld(WF 8, Nat.mul 12 f, 4095)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨[], (fun _ hg => nomatch hg), fun _ _ => rfl, fun _ _ => rfl,
        fun _ _ => rfl⟩
    have hc := hw k hk
    have hbk := hb k hk
    unfold wfK at hc
    unfold bfK at hbk
    simp only [strictB_eq] at hc hbk
    have e8 : Nat.sub (8 + k) 8 = k := Nat.add_sub_cancel_left 8 k
    simp only [blt_ff (Nat.le_add_right 8 k), recB_ff, e8] at hc
    simp only [beq_ff (Nat.pos_iff_ne_zero.1 hpos), recB_ff] at hc hbk
    obtain ⟨h1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨h2, h3⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    obtain ⟨-, hbk⟩ := (CFSG.KS.bAnd_iff _ _).1 hbk
    obtain ⟨-, hbk⟩ := (CFSG.KS.bAnd_iff _ _).1 hbk
    obtain ⟨b3, b4⟩ := (CFSG.KS.bAnd_iff _ _).1 hbk
    have hpar : fld(BF k, 108, 4095) < k := Nat.le_of_ble_eq_true h1
    have hg : Nat.shiftRight (BF k) 120 < 19 := Nat.le_of_ble_eq_true h2
    obtain ⟨l, hl, hfix, hB, hW⟩ := ih _ hpar (by omega)
    refine ⟨Nat.shiftRight (BF k) 120 :: l, fun g hm => ?_, fun m hm => ?_, fun p hp => ?_,
      fun f hf => ?_⟩
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hg
      · exact hl g hm
    · rw [wAp_cons, hfix m hm]
      exact Nat.eq_of_beq_eq_true (allBlk_spec0 b3 m hm)
    · rw [wAp_cons, ← hB p hp]
      exact Nat.eq_of_beq_eq_true (allBlk_spec0 b4 p hp)
    · rw [wAp_cons, ← hW f hf]
      exact Nat.eq_of_beq_eq_true (allBlk_spec0 h3 f hf)

theorem wf8_sound {WF OF BF S : Nat → Nat} (h : wfK WF OF BF S 8 = true) :
    ∀ p < 8, fld(BF 0, Nat.mul 12 (Nat.succ p), 4095) = ap (OF 4) p ∧
      fld(WF 8, Nat.mul 24 p, 4095) = fld(WF p, 24, 4095) ∧
      fld(WF 8, Nat.add (Nat.mul 24 p) 12, 4095) = fld(WF p, 36, 4095) := by
  unfold wfK at h
  simp only [strictB_eq, blt88, sub88, beq00, recB_tt, recB_ff] at h
  intro p hp
  have e := allBlk_spec0 h p hp
  obtain ⟨e1, e⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  obtain ⟨e2, e3⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2, Nat.eq_of_beq_eq_true e3⟩

theorem wf_sound {WF OF BF S : Nat → Nat} (hw : ∀ u < 728, wfK WF OF BF S u = true)
    (hb : ∀ k < 720, bfK BF S k = true) :
    ∀ k < 720, ∀ p < 8, ∃ l : List Nat, (∀ g ∈ l, g < 19) ∧ (∀ m < 3, wAp S l (bp m) = bp m) ∧
      wAp S l (bp 3) = fld(BF k, 0, 4095) ∧
      wAp S l (ap (OF 4) 0) = fld(BF k, Nat.mul 12 (Nat.succ p), 4095) ∧
      ∀ q < 2, fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095) =
        wAp S l (ap (OF 5) q) := by
  intro k hk p hp
  have h4 := wf4_sound (fun u hu => hw u (by omega)) p (by omega)
  have h8 := wf8_sound (hw 8 (by omega)) p hp
  have hB := wfB_sound (fun k hk => hw (8 + k) (by omega)) hb k hk
  have hr := (bf_root (hb 0 (by omega))).1
  obtain ⟨lp, hlp, fixp, o4p, w0, w1⟩ := h4
  obtain ⟨b8, w80, w81⟩ := h8
  obtain ⟨lk, hlk, fixk, hBk, hWk⟩ := hB
  refine ⟨lk ++ lp, fun g hm => ?_, fun m hm => ?_, ?_, ?_, fun q hq => ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · exact hlk g hm
    · exact hlp g hm
  · rw [wAp_append, fixp m (by omega), fixk m hm]
  · rw [wAp_append, fixp 3 (by omega)]
    have e := hBk 0 (by omega)
    change fld(BF k, 0, 4095) = wAp S lk (fld(BF 0, 0, 4095)) at e
    rw [e, hr]
    rfl
  · rw [wAp_append, o4p, ← b8]
    exact (hBk (Nat.succ p) (by omega)).symm
  · rw [wAp_append]
    have hf : Nat.add (Nat.mul 2 p) q < 16 := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    have e := hWk _ hf
    change fld(WF (Nat.add 8 k), _, 4095) = _ at e
    rw [e]
    obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · have i0 : Nat.mul 12 (Nat.add (Nat.mul 2 p) 0) = Nat.mul 24 p := by
        simp only [Nat.add_eq, Nat.mul_eq]
        omega
      rw [i0, w80, w0]
    · have i1 : Nat.mul 12 (Nat.add (Nat.mul 2 p) 1) = Nat.add (Nat.mul 24 p) 12 := by
        simp only [Nat.add_eq, Nat.mul_eq]
        omega
      rw [i1, w81, w1]

theorem codeMem_lt9 {W x : Nat} (h : codeMem W x) (hW : Nat.shiftRight W 126 = 0)
    (hx : x ≠ 0) : ∃ s < 9, fld(W, Nat.mul 14 s, 16383) = x := by
  obtain ⟨i, hi⟩ := h
  rcases Nat.lt_or_ge i 9 with hlt | hge
  · exact ⟨i, hlt, hi⟩
  exfalso
  apply hx
  rw [← hi]
  change (W >>> (14 * i)) &&& 16383 = 0
  have e : W >>> (14 * i) = (W >>> 126) >>> (14 * i - 126) := by
    rw [← Nat.shiftRight_add]
    congr 1
    omega
  have hW' : W >>> 126 = 0 := hW
  rw [e, hW', Nat.zero_shiftRight, Nat.zero_and]

@[expose] noncomputable def leafFull (BF WF : Nat → Nat) (a : Nat → Nat) (k p q : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (a (bp 0)) (Nat.shiftLeft (a (bp 1)) 12))
      (Nat.shiftLeft (a (bp 2)) 24))
    (Nat.lor (Nat.shiftLeft (a (fld(BF k, 0, 4095))) 36)
      (Nat.shiftLeft (a (fld(BF k, Nat.mul 12 (Nat.succ p), 4095))) 48)))
    (Nat.shiftLeft (a (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095))) 60)

@[expose] noncomputable def leafA (T K : Nat → Nat) (n : Nat) (x : Nat) : Nat :=
  ap (T (fld(K n, 0, 65535))) (ap (T (fld(K n, 16, 65535))) (ap (T (fld(K n, 32, 65535))) x))

theorem leafK_sound {T D M BF WF X E K CK : Nat → Nat} {j n offC szC : Nat}
    (h : leafK T D M BF WF X E K CK j n offC szC = true) :
    Nat.shiftRight (Nat.shiftRight (K n) 48) 126 = 0 ∧
    ∀ s < 9, ∀ k p : Nat, fld(Nat.shiftRight (K n) 48, Nat.mul 14 s, 16383) = 8 * k + p + 1 →
      p < 8 → k < 720 ∧ ∀ q < 2,
        leafV M (fun e => D (Nat.add (Nat.mul 27 j) e)) CK (X j) offC szC
          (leafFull BF WF (leafA T K n) k p q)
          (leafA T K n (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095)))
          (fld(E n, Nat.mul 16 (Nat.add (Nat.mul 2 s) q), 65535)) = true := by
  unfold leafK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun s hs k p hf hp => ?_⟩
  have e := allBlk_spec0 h2 s hs
  rw [hf] at e
  simp only [beq_ff (by omega : 8 * k + p + 1 ≠ 0), recB_ff] at e
  have ek : Nat.div (Nat.sub (8 * k + p + 1) 1) 8 = k := by
    change (8 * k + p + 1 - 1) / 8 = k
    omega
  have ep : Nat.mod (Nat.sub (8 * k + p + 1) 1) 8 = p := by
    change (8 * k + p + 1 - 1) % 8 = p
    omega
  rw [ek, ep] at e
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  refine ⟨Nat.le_of_ble_eq_true e1, fun q hq => ?_⟩
  exact allBlk_spec0 e2 q hq

theorem leafV_sound {M Dj CK : Nat → Nat} {h offC szC full v ef : Nat}
    (hv : leafV M Dj CK h offC szC full v ef = true) :
    (∃ i < szC, fld(CK (Nat.add offC i), 0, m72) = full) ∨ relK Dj h full = false ∨
      ∃ mm < 5, ∃ e < 27, eb M (ap (Dj e) (cg full mm)) v ≠ eb M (ap (Dj e) (bp mm)) (bp 5) := by
  unfold leafV at hv
  cases c1 : Nat.ble 32768 ef
  · simp only [c1, recB_ff] at hv
    cases c2 : Nat.beq ef 1
    · simp only [c2, recB_ff, strictB_eq] at hv
      obtain ⟨-, hv⟩ := (CFSG.KS.bAnd_iff _ _).1 hv
      obtain ⟨w1, w2⟩ := (CFSG.KS.bAnd_iff _ _).1 hv
      have hw : Nat.sub ef 2 < 135 := Nat.le_of_ble_eq_true w1
      refine Or.inr (Or.inr ⟨Nat.div (Nat.sub ef 2) 27, ?_, Nat.mod (Nat.sub ef 2) 27, ?_, ?_⟩)
      · change (ef - 2) / 27 < 5
        change ef - 2 < 135 at hw
        omega
      · exact Nat.mod_lt _ (by omega)
      · exact Nat.ne_of_beq_eq_false (not_tt w2)
    · simp only [c2, recB_tt] at hv
      exact Or.inr (Or.inl (not_tt hv))
  · simp only [c1, recB_tt, strictB_eq] at hv
    obtain ⟨w1, w2⟩ := (CFSG.KS.bAnd_iff _ _).1 hv
    exact Or.inl ⟨_, Nat.le_of_ble_eq_true w1, Nat.eq_of_beq_eq_true w2⟩

theorem orbK_lt {CK G : Nat → Nat} {gof ng off sz : Nat}
    (h : ∀ i < sz, orbK CK G gof ng off sz i = true) :
    ∀ i i', i < i' → i' < sz →
      fld(CK (Nat.add off i), 0, m72) < fld(CK (Nat.add off i'), 0, m72) := by
  have step : ∀ i, i + 1 < sz →
      fld(CK (Nat.add off i), 0, m72) < fld(CK (Nat.add off (i + 1)), 0, m72) := by
    intro i hi
    have hc := h (i + 1) hi
    unfold orbK at hc
    simp only [strictB_eq] at hc
    obtain ⟨h1, -⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
    simp only [beq_ff (by omega : i + 1 ≠ 0), recB_ff] at h1
    have e : Nat.sub (Nat.add off (i + 1)) 1 = Nat.add off i := by
      simp only [Nat.add_eq, Nat.sub_eq]
      omega
    rw [e] at h1
    exact Nat.le_of_ble_eq_true h1
  intro i i' hii' hi'
  induction i' with
  | zero => exact absurd hii' (Nat.not_lt_zero _)
  | succ i' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hii' with hlt | rfl
    · exact Nat.lt_trans (ih hlt (by omega)) (step i' hi')
    · exact step i hi'

theorem orbK_inj {CK G : Nat → Nat} {gof ng off sz : Nat}
    (h : ∀ i < sz, orbK CK G gof ng off sz i = true) :
    ∀ i < sz, ∀ i' < sz,
      fld(CK (Nat.add off i), 0, m72) = fld(CK (Nat.add off i'), 0, m72) → i = i' := by
  intro i hi i' hi' he
  rcases Nat.lt_trichotomy i i' with hlt | heq | hgt
  · exact absurd he (Nat.ne_of_lt (orbK_lt h i i' hlt hi'))
  · exact heq
  · exact absurd he (Nat.ne_of_gt (orbK_lt h i' i hgt hi))

theorem orbK_mem {CK G : Nat → Nat} {gof ng off sz : Nat}
    (h : ∀ i < sz, orbK CK G gof ng off sz i = true) (Q : Nat → Prop) (hb : Q baseKey)
    (hg : ∀ m < ng, ∀ c, Q c → Q (kAp (G (Nat.add gof m)) c)) :
    ∀ i < sz, Q (fld(CK (Nat.add off i), 0, m72)) := by
  have key : ∀ d, ∀ i < sz, fld(CK (Nat.add off i), 72, 255) = d →
      Q (fld(CK (Nat.add off i), 0, m72)) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      have hc := h i hi
      unfold orbK at hc
      simp only [strictB_eq] at hc
      obtain ⟨-, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨hc, -⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      rw [hd] at hc
      simp only [beq00, recB_tt] at hc
      rw [Nat.eq_of_beq_eq_true hc]
      exact hb
    | succ d ih =>
      intro i hi hd
      have hc := h i hi
      unfold orbK at hc
      simp only [strictB_eq] at hc
      obtain ⟨-, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨hc, -⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      rw [hd] at hc
      simp only [beq_ff (by omega : d + 1 ≠ 0), recB_ff] at hc
      obtain ⟨c1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨c2, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨c3, c4⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      have hpa : fld(CK (Nat.add off i), 80, 4095) < sz := Nat.le_of_ble_eq_true c1
      have hgg : fld(CK (Nat.add off i), 92, 15) < ng := Nat.le_of_ble_eq_true c2
      have hdp := Nat.eq_of_beq_eq_true c3
      rw [Nat.eq_of_beq_eq_true c4]
      exact hg _ hgg _ (ih _ hpa (Nat.succ.inj hdp))
  exact fun i hi => key _ i hi rfl

theorem orbK_closed {CK G : Nat → Nat} {gof ng off sz : Nat}
    (h : ∀ i < sz, orbK CK G gof ng off sz i = true) :
    ∀ i < sz, ∀ m < ng, ∃ x < sz,
      fld(CK (Nat.add off x), 0, m72) = kAp (G (Nat.add gof m)) (fld(CK (Nat.add off i), 0, m72)) := by
  intro i hi m hm
  have hc := h i hi
  unfold orbK at hc
  simp only [strictB_eq] at hc
  obtain ⟨-, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
  obtain ⟨-, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
  have e := allBlk_spec0 hc m hm
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨_, Nat.le_of_ble_eq_true e1, Nat.eq_of_beq_eq_true e2⟩

theorem subK_sound {UK CK : Nat → Nat} {offU offC szC i : Nat}
    (h : subK UK CK offU offC szC i = true) :
    ∃ x < szC, fld(CK (Nat.add offC x), 0, m72) = fld(UK (Nat.add offU i), 0, m72) := by
  unfold subK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  exact ⟨_, Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem commK_sound {G D : Nat → Nat} {gof j m : Nat} (h : commK G D gof j m = true) :
    ∀ e, (e = 9 ∨ e = 3 ∨ e = 1) →
      kAp (G (Nat.add gof m)) (kAp (D (Nat.add (Nat.mul 27 j) e)) baseKey) =
        kAp (D (Nat.add (Nat.mul 27 j) e)) (kAp (G (Nat.add gof m)) baseKey) := by
  unfold commK at h
  simp only [strictB_eq] at h
  rintro e (rfl | rfl | rfl)
  · exact Nat.eq_of_beq_eq_true (allBlk_spec0 h 0 (by omega))
  · exact Nat.eq_of_beq_eq_true (allBlk_spec0 h 1 (by omega))
  · exact Nat.eq_of_beq_eq_true (allBlk_spec0 h 2 (by omega))

theorem normK_sound {NF CG UG UK : Nat → Nat} {j m gofC gofU ngU offU szU : Nat}
    (h : normK NF CG UG UK j m gofC gofU ngU offU szU = true) :
    kAp (CG (Nat.add gofC m)) (fld(NF (Nat.add (Nat.mul 8 j) m), 0, m72)) = baseKey ∧
    ∀ t < ngU, ∃ x < szU, fld(UK (Nat.add offU x), 0, m72) =
      kAp (CG (Nat.add gofC m)) (kAp (UG (Nat.add gofU t)) (fld(NF (Nat.add (Nat.mul 8 j) m), 0, m72))) := by
  unfold normK at h
  simp only [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun t ht => ?_⟩
  have e := allBlk_spec0 h2 t ht
  obtain ⟨e1, e2⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨_, Nat.le_of_ble_eq_true e1, Nat.eq_of_beq_eq_true e2⟩

theorem relV_sound {Dj : Nat → Nat} {h lv : Nat} (hv : relV Dj h lv = true) : RelV Dj h lv := by
  unfold relV at hv
  intro t ht
  have e := allBlk_spec0 hv t ht
  simp only [strictB_eq] at e
  obtain ⟨e1, e⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  obtain ⟨e2, e⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  obtain ⟨e3, e4⟩ := (CFSG.KS.bAnd_iff _ _).1 e
  exact ⟨Nat.le_of_ble_eq_true e2, Nat.le_of_ble_eq_true e3, Nat.le_of_ble_eq_true e1,
    Nat.eq_of_beq_eq_true e4⟩

theorem dfK_sound {DF : Nat → Nat} {R j e : Nat} (h : dfK DF R j e = true) :
    (e = 0 → ∀ i < 3510, ap (DF (27 * j + e)) i = i) ∧
    (e % 3 ≠ 0 → ∀ i < 3510,
      ap (DF (27 * j + e)) i = ap (DF (27 * j + e - 1)) (ap (rowR R (3 * j + 2)) i)) ∧
    (0 < e → e % 3 = 0 → e % 9 ≠ 0 → ∀ i < 3510,
      ap (DF (27 * j + e)) i = ap (DF (27 * j + e - 3)) (ap (rowR R (3 * j + 1)) i)) ∧
    (0 < e → e % 9 = 0 → ∀ i < 3510,
      ap (DF (27 * j + e)) i = ap (DF (27 * j + e - 9)) (ap (rowR R (3 * j)) i)) := by
  unfold dfK at h
  simp only [strictB_eq] at h
  refine ⟨fun he i hi => ?_, fun h3 i hi => ?_, fun he h3 h9 i hi => ?_, fun he h9 i hi => ?_⟩
  · subst he
    simp only [beq00, recB_tt] at h
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
  · have he : e ≠ 0 := fun he => h3 (by subst he; rfl)
    have c3 : Nat.beq (Nat.mod e 3) 0 = false := beq_ff h3
    simp only [beq_ff he, recB_ff, c3, recN_ff] at h
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
  · have c3 : Nat.beq (Nat.mod e 3) 0 = true := beq_tt h3
    have c9 : Nat.beq (Nat.mod e 9) 0 = false := beq_ff h9
    simp only [beq_ff (Nat.pos_iff_ne_zero.1 he), recB_ff, c3, recN_tt, c9, recN_ff] at h
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
  · have c3 : Nat.beq (Nat.mod e 3) 0 = true := beq_tt (by change e % 3 = 0; omega)
    have c9 : Nat.beq (Nat.mod e 9) 0 = true := beq_tt h9
    simp only [beq_ff (Nat.pos_iff_ne_zero.1 he), recB_ff, c3, recN_tt, c9] at h
    exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)

end CFSG.KC.Fi22Twist

end
