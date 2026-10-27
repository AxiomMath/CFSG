module

public import Certificates.Data.Kernel.Spor.F3Lane
public import CFSG.F3.ConjSpec

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

theorem strictT_eq {α : Type} (y : Nat) (k : Nat → α) : strictT y k = k y := by
  cases y <;> rfl

theorem mk_eq (d : Nat) : mk d = 2 ^ d - 1 := by
  unfold mk
  change 1 <<< d - 1 = _
  rw [Nat.one_shiftLeft]

theorem V.ext' {a b : V} (hp : a.p = b.p) (hm : a.m = b.m) : a = b := by
  cases a
  cases b
  simp only at hp hm
  rw [hp, hm]

theorem blk_p (d : Nat) (L : V) (b k : Nat) :
    (blk d L b).p.testBit k = (decide (k < d) && L.p.testBit (d * b + k)) := by
  change (L.p >>> (d * b) &&& mk d).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, mk_eq, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem blk_m (d : Nat) (L : V) (b k : Nat) :
    (blk d L b).m.testBit k = (decide (k < d) && L.m.testBit (d * b + k)) := by
  change (L.m >>> (d * b) &&& mk d).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, mk_eq, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem blk_p_lt (d : Nat) (L : V) (b : Nat) : (blk d L b).p < 2 ^ d := by
  change (L.p >>> (d * b) &&& mk d) < 2 ^ d
  rw [mk_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)

theorem blk_m_lt (d : Nat) (L : V) (b : Nat) : (blk d L b).m < 2 ^ d := by
  change (L.m >>> (d * b) &&& mk d) < 2 ^ d
  rw [mk_eq]
  exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos d) Nat.one_pos)

theorem blk_add (d : Nat) (a c : V) (b : Nat) : blk d (a.add c) b = (blk d a b).add (blk d c b) := by
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · rw [blk_p, (V.add_bits _ _ k).1, (V.add_bits _ _ _).1, blk_p, blk_p, blk_m, blk_m]
    by_cases hk : k < d <;> simp [hk]
  · rw [blk_m, (V.add_bits _ _ k).2, (V.add_bits _ _ _).2, blk_p, blk_p, blk_m, blk_m]
    by_cases hk : k < d <;> simp [hk]

theorem blk_zero (d b : Nat) : blk d V.zero b = V.zero := by
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · rw [blk_p]
    simp [V.zero]
  · rw [blk_m]
    simp [V.zero]

theorem add_zero' (a : V) : a.add ⟨0, 0⟩ = a := by
  apply V.ext' <;> simp [V.add]

theorem spreadE_testBit {d : Nat} (hd : 0 < d) (nb i : Nat) :
    (spreadE d nb).testBit i = decide (d ∣ i ∧ i / d < nb) := by
  induction nb with
  | zero =>
    change Nat.testBit 0 i = _
    simp
  | succ nb ih =>
    change (spreadE d nb ||| 1 <<< (d * nb)).testBit i = _
    rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hdi : d ∣ i
    · obtain ⟨q, rfl⟩ := hdi
      rw [Nat.mul_div_cancel_left _ hd]
      by_cases hq : q = nb
      · subst hq
        simp
      · have : d * nb ≠ d * q := fun e => hq (Nat.eq_of_mul_eq_mul_left hd e).symm
        simp only [dvd_mul_right, true_and, this, decide_false, Bool.or_false]
        by_cases h : q < nb
        · have : q < nb + 1 := by omega
          simp [h, this]
        · have : ¬ q < nb + 1 := by omega
          simp [h, this]
    · have : d * nb ≠ i := fun e => hdi ⟨nb, e.symm⟩
      simp [hdi, this]

theorem lt_two_of_testBit {s : Nat} (h : ∀ i, 1 ≤ i → s.testBit i = false) : s < 2 := by
  have := Nat.lt_pow_two_of_testBit s (n := 1) (fun i hi => h i hi)
  simpa using this

theorem testBit_spread {d : Nat} (hd : 0 < d) {y : Nat} (hy : y < 2 ^ d) (k : Nat) (hk : k < d) :
    ∀ (b S : Nat), (∀ i, S.testBit i = true → d ∣ i) →
      (S * y).testBit (d * b + k) = (S.testBit (d * b) && y.testBit k) := by
  intro b
  induction b with
  | zero =>
    intro S hS
    have hS0 : S % 2 ^ d < 2 := lt_two_of_testBit fun i hi => by
      rw [Nat.testBit_mod_two_pow]
      by_cases hid : i < d
      · have : ¬ S.testBit i = true := fun h => by
          obtain ⟨q, hq⟩ := hS i h
          rcases q with _ | q
          · omega
          · have : d ≤ i := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
            omega
        simp [hid, this]
      · simp [hid]
    have e : S * y = 2 ^ d * (S / 2 ^ d * y) + S % 2 ^ d * y := by
      conv_lhs => rw [← Nat.div_add_mod S (2 ^ d)]
      ring
    have hlt : S % 2 ^ d * y < 2 ^ d := by
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> omega
    rw [Nat.mul_zero, Nat.zero_add, e, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left hk]
    have h0 : S.testBit 0 = decide (S % 2 ^ d = 1) := by
      have : S.testBit 0 = (S % 2 ^ d).testBit 0 := by
        rw [Nat.testBit_mod_two_pow]
        simp [hd]
      rw [this]
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> rfl
    rw [h0]
    rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> simp
  | succ b ih =>
    intro S hS
    have e : S * y = 2 ^ d * (S / 2 ^ d * y) + S % 2 ^ d * y := by
      conv_lhs => rw [← Nat.div_add_mod S (2 ^ d)]
      ring
    have hS0 : S % 2 ^ d < 2 := lt_two_of_testBit fun i hi => by
      rw [Nat.testBit_mod_two_pow]
      by_cases hid : i < d
      · have : ¬ S.testBit i = true := fun h => by
          obtain ⟨q, hq⟩ := hS i h
          rcases q with _ | q
          · omega
          · have : d ≤ i := by rw [hq]; exact Nat.le_mul_of_pos_right _ (by omega)
            omega
        simp [hid, this]
      · simp [hid]
    have hlt : S % 2 ^ d * y < 2 ^ d := by
      rcases (by omega : S % 2 ^ d = 0 ∨ S % 2 ^ d = 1) with h | h <;> rw [h] <;> omega
    have hS' : ∀ i, (S / 2 ^ d).testBit i = true → d ∣ i := by
      intro i hi
      rw [Nat.testBit_div_two_pow] at hi
      have := hS _ hi
      exact (Nat.dvd_add_right (dvd_refl d)).1 (by rw [Nat.add_comm]; exact this)
    have h1 : ¬ d * (b + 1) + k < d := by
      have := Nat.le_mul_of_pos_right d (by omega : 0 < b + 1)
      omega
    have e1 : d * (b + 1) + k - d = d * b + k := by rw [Nat.mul_succ]; omega
    rw [e, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_right h1, e1, ih _ hS']
    rw [Nat.testBit_div_two_pow]
    rfl

theorem spread_bits {d nb : Nat} (hd : 0 < d) (X : Nat) (j i : Nat) :
    (Nat.land (Nat.shiftRight X j) (spreadE d nb)).testBit i = true → d ∣ i := by
  intro h
  change (X >>> j &&& spreadE d nb).testBit i = true at h
  rw [Nat.testBit_and, spreadE_testBit hd] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

theorem spread_at {d nb : Nat} (hd : 0 < d) (X : Nat) (j : Nat) {b : Nat} (hb : b < nb) :
    (Nat.land (Nat.shiftRight X j) (spreadE d nb)).testBit (d * b) = X.testBit (d * b + j) := by
  change (X >>> j &&& spreadE d nb).testBit (d * b) = _
  rw [Nat.testBit_and, spreadE_testBit hd, Nat.testBit_shiftRight, Nat.mul_div_cancel_left _ hd,
    Nat.add_comm j]
  simp [hb]

theorem blk_term {d nb : Nat} (hd : 0 < d) (X y : V) (hyp : y.p < 2 ^ d) (hym : y.m < 2 ^ d)
    (j : Nat) {b : Nat} (hb : b < nb) :
    blk d ⟨Nat.lor (Nat.mul (Nat.land (Nat.shiftRight X.p j) (spreadE d nb)) y.p)
        (Nat.mul (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb)) y.m),
      Nat.lor (Nat.mul (Nat.land (Nat.shiftRight X.p j) (spreadE d nb)) y.m)
        (Nat.mul (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb)) y.p)⟩ b =
      if X.p.testBit (d * b + j) then y
      else if X.m.testBit (d * b + j) then y.neg else ⟨0, 0⟩ := by
  have sp := spread_at (nb := nb) hd X.p j hb
  have sm := spread_at (nb := nb) hd (Nat.xor X.m (Nat.land X.m X.p)) j hb
  have hm' : (Nat.xor X.m (Nat.land X.m X.p)).testBit (d * b + j) =
      (X.m.testBit (d * b + j) && !X.p.testBit (d * b + j)) := by
    change (X.m ^^^ (X.m &&& X.p)).testBit _ = _
    rw [Nat.testBit_xor, Nat.testBit_and]
    cases X.m.testBit (d * b + j) <;> cases X.p.testBit (d * b + j) <;> rfl
  have key : ∀ (y' : Nat), y' < 2 ^ d → ∀ (Z : Nat) k, k < d →
      (Nat.mul (Nat.land (Nat.shiftRight Z j) (spreadE d nb)) y').testBit (d * b + k) =
        (Z.testBit (d * b + j) && y'.testBit k) := by
    intro y' hy' Z k hk
    rw [← spread_at (nb := nb) hd Z j hb]
    exact testBit_spread hd hy' k hk b _ (spread_bits hd Z j)
  have hor : ∀ a c i : Nat, (Nat.lor a c).testBit i = (a.testBit i || c.testBit i) :=
    fun a c i => Nat.testBit_or a c i
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · rw [blk_p]
    by_cases hk : k < d
    · dsimp only
      rw [hor, key _ hyp _ k hk, key _ hym _ k hk, hm']
      simp only [hk, decide_true, Bool.true_and]
      by_cases h1 : X.p.testBit (d * b + j) = true
      · simp [h1]
      · by_cases h2 : X.m.testBit (d * b + j) = true
        · simp [h1, h2, V.neg]
        · simp [h1, h2]
    · simp only [hk, decide_false, Bool.false_and]
      have : ∀ v : Nat, v < 2 ^ d → v.testBit k = false := fun v hv =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      split_ifs
      · exact (this _ hyp).symm
      · exact (this _ hym).symm
      · simp
  · rw [blk_m]
    by_cases hk : k < d
    · dsimp only
      rw [hor, key _ hym _ k hk, key _ hyp _ k hk, hm']
      simp only [hk, decide_true, Bool.true_and]
      by_cases h1 : X.p.testBit (d * b + j) = true
      · simp [h1]
      · by_cases h2 : X.m.testBit (d * b + j) = true
        · simp [h1, h2, V.neg]
        · simp [h1, h2]
    · simp only [hk, decide_false, Bool.false_and]
      have : ∀ v : Nat, v < 2 ^ d → v.testBit k = false := fun v hv =>
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))
      split_ifs
      · exact (this _ hym).symm
      · exact (this _ hyp).symm
      · simp

theorem blk_rmStep {d nb : Nat} (hd : 0 < d) (X y acc : V) (hyp : y.p < 2 ^ d) (hym : y.m < 2 ^ d)
    {j : Nat} (hj : j < d) {b : Nat} (hb : b < nb) (Yr : Array V) (hY : Yr[j]! = y) :
    blk d (rmStep (spreadE d nb) X y j acc) b = combStep Yr (blk d X b) j (blk d acc b) := by
  unfold rmStep
  rw [strictT_eq, strictT_eq, blk_add, blk_term hd X y hyp hym j hb]
  unfold combStep
  rw [blk_p, blk_m, hY]
  simp only [hj, decide_true, Bool.true_and]
  split_ifs
  · rfl
  · rfl
  · exact add_zero' _

theorem blk_rmK_n {d nb : Nat} (hd : 0 < d) (X : V) (Y : Nat → V)
    (hYb : ∀ j < d, (Y j).p < 2 ^ d ∧ (Y j).m < 2 ^ d) {b : Nat} (hb : b < nb) (Yr : Array V)
    (hY : ∀ j < d, Yr[j]! = Y j) : ∀ n ≤ d,
      blk d (Nat.rec (motive := fun _ => V) V.zero
        (fun j acc => strictT acc.p fun ap => strictT acc.m fun am =>
          rmStep (spreadE d nb) X (Y j) j ⟨ap, am⟩) n) b =
        Nat.fold n (fun j _ acc => combStep Yr (blk d X b) j acc) V.zero := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.fold_zero]
    exact blk_zero d b
  | succ n ih =>
    intro hn
    rw [Nat.fold_succ]
    change blk d (strictT _ fun ap => strictT _ fun am => rmStep _ X (Y n) n ⟨ap, am⟩) b = _
    rw [strictT_eq, strictT_eq, ← ih (by omega)]
    rw [blk_rmStep hd X (Y n) _ (hYb n (by omega)).1 (hYb n (by omega)).2 (by omega) hb Yr
      (hY n (by omega))]

theorem blk_rmK {d nb : Nat} (hd : 0 < d) (X : V) (Y : Nat → V)
    (hYb : ∀ j < d, (Y j).p < 2 ^ d ∧ (Y j).m < 2 ^ d) {b : Nat} (hb : b < nb) (Yr : Array V)
    (hY : ∀ j < d, Yr[j]! = Y j) :
    blk d (rmK d (spreadE d nb) X Y) b = comb d Yr (blk d X b) :=
  blk_rmK_n hd X Y hYb hb Yr hY d (Nat.le_refl _)

theorem blk_wf (d : Nat) {L : V} (h : L.wf = true) (b : Nat) : (blk d L b).wf = true := by
  apply V.wf_of_bits
  intro k
  rw [blk_p, blk_m]
  have := V.not_both h (d * b + k)
  cases hk : decide (k < d) <;> simp_all

theorem addW_eq {a b : V} (ha : a.wf = true) (hb : b.wf = true) : addW a b = a.add b := by
  have h1 := V.not_both ha
  have h2 := V.not_both hb
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · change ((a.m ||| b.m) ^^^ ((a.p ||| b.m) ^^^ (a.m ||| b.p))).testBit k = _
    rw [(V.add_bits a b k).1]
    simp only [Nat.testBit_xor, Nat.testBit_or]
    have h1 := h1 k
    have h2 := h2 k
    revert h1 h2
    cases a.p.testBit k <;> cases a.m.testBit k <;> cases b.p.testBit k <;> cases b.m.testBit k <;>
      decide
  · change ((a.p ||| b.p) ^^^ ((a.p ||| b.m) ^^^ (a.m ||| b.p))).testBit k = _
    rw [(V.add_bits a b k).2]
    simp only [Nat.testBit_xor, Nat.testBit_or]
    have h1 := h1 k
    have h2 := h2 k
    revert h1 h2
    cases a.p.testBit k <;> cases a.m.testBit k <;> cases b.p.testBit k <;> cases b.m.testBit k <;>
      decide

theorem term_wf {d nb : Nat} (hd : 0 < d) (X y : V) (hy : y.wf = true) (hyp : y.p < 2 ^ d)
    (hym : y.m < 2 ^ d) (j : Nat) :
    (⟨Nat.lor (Nat.mul (Nat.land (Nat.shiftRight X.p j) (spreadE d nb)) y.p)
        (Nat.mul (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb)) y.m),
      Nat.lor (Nat.mul (Nat.land (Nat.shiftRight X.p j) (spreadE d nb)) y.m)
        (Nat.mul (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb))
          y.p)⟩ : V).wf = true := by
  apply V.wf_of_bits
  intro i
  obtain ⟨b, k, hk, rfl⟩ : ∃ b k, k < d ∧ i = d * b + k :=
    ⟨i / d, i % d, Nat.mod_lt _ hd, (Nat.div_add_mod i d).symm⟩
  have key : ∀ (y' : Nat), y' < 2 ^ d → ∀ (Z : Nat),
      (Nat.mul (Nat.land (Nat.shiftRight Z j) (spreadE d nb)) y').testBit (d * b + k) =
        ((Nat.land (Nat.shiftRight Z j) (spreadE d nb)).testBit (d * b) && y'.testBit k) :=
    fun y' hy' Z => testBit_spread hd hy' k hk b _ (spread_bits hd Z j)
  have hor : ∀ a c i : Nat, (Nat.lor a c).testBit i = (a.testBit i || c.testBit i) :=
    fun a c i => Nat.testBit_or a c i
  have hs : ((Nat.land (Nat.shiftRight X.p j) (spreadE d nb)).testBit (d * b) &&
      (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb)).testBit
        (d * b)) = false := by
    change ((X.p >>> j &&& spreadE d nb).testBit (d * b) &&
      ((X.m ^^^ (X.m &&& X.p)) >>> j &&& spreadE d nb).testBit (d * b)) = false
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_xor]
    cases X.p.testBit (j + d * b) <;> cases X.m.testBit (j + d * b) <;> simp
  have hy' := V.not_both hy k
  dsimp only
  rw [hor, hor, key _ hyp, key _ hym, key _ hym, key _ hyp]
  revert hs hy'
  generalize (Nat.land (Nat.shiftRight X.p j) (spreadE d nb)).testBit (d * b) = s1
  generalize (Nat.land (Nat.shiftRight (Nat.xor X.m (Nat.land X.m X.p)) j) (spreadE d nb)).testBit
    (d * b) = s2
  generalize y.p.testBit k = t1
  generalize y.m.testBit k = t2
  cases s1 <;> cases s2 <;> cases t1 <;> cases t2 <;> decide

theorem rmStepW_eq {d nb : Nat} (hd : 0 < d) (X y acc : V) (hacc : acc.wf = true)
    (hy : y.wf = true) (hyp : y.p < 2 ^ d) (hym : y.m < 2 ^ d) (j : Nat) :
    rmStepW (spreadE d nb) ⟨X.p, Nat.xor X.m (Nat.land X.m X.p)⟩ y j acc =
      rmStep (spreadE d nb) X y j acc := by
  unfold rmStep
  rw [strictT_eq, strictT_eq]
  exact addW_eq hacc (term_wf hd X y hy hyp hym j)

theorem rmKW_succ (n E : Nat) (X : V) (Y : Nat → V) :
    rmKW (n + 1) E X Y = rmStepW E X (Y n) n (rmKW n E X Y) := by
  change strictT (rmKW n E X Y).p
    (fun ap => strictT (rmKW n E X Y).m fun am => rmStepW E X (Y n) n ⟨ap, am⟩) = _
  rw [strictT_eq, strictT_eq]

theorem rmK_succ (n E : Nat) (X : V) (Y : Nat → V) :
    rmK (n + 1) E X Y = rmStep E X (Y n) n (rmK n E X Y) := by
  change strictT (rmK n E X Y).p
    (fun ap => strictT (rmK n E X Y).m fun am => rmStep E X (Y n) n ⟨ap, am⟩) = _
  rw [strictT_eq, strictT_eq]

theorem rmKW_eq {d nb : Nat} (hd : 0 < d) (X : V) (Y : Nat → V) : ∀ n,
    (∀ j < n, (Y j).wf = true ∧ (Y j).p < 2 ^ d ∧ (Y j).m < 2 ^ d) →
      rmKW n (spreadE d nb) ⟨X.p, Nat.xor X.m (Nat.land X.m X.p)⟩ Y = rmK n (spreadE d nb) X Y ∧
        (rmK n (spreadE d nb) X Y).wf = true
  | 0, _ => ⟨rfl, by
      change V.zero.wf = true
      exact V.wf_of_bits fun j => by simp [V.zero]⟩
  | n + 1, h => by
    obtain ⟨e, hw⟩ := rmKW_eq hd X Y n (fun j hj => h j (by omega))
    obtain ⟨hyw, hyp, hym⟩ := h n (by omega)
    rw [rmKW_succ, rmK_succ, e, rmStepW_eq hd X (Y n) _ hw hyw hyp hym n]
    refine ⟨rfl, ?_⟩
    unfold rmStep
    rw [strictT_eq, strictT_eq]
    exact V.wf_add hw (term_wf hd X (Y n) hyw hyp hym n)

theorem mulLane_eq {d nb : Nat} (hd : 0 < d) (X Y : V) :
    mulLane d (spreadE d nb) X Y = rmK d (spreadE d nb) X (blk d Y) := by
  unfold mulLane
  cases h : Nat.beq (Nat.land Y.p Y.m) 0
  · rfl
  · change strictT (Nat.xor X.m (Nat.land X.m X.p))
      (fun xm => rmKW d (spreadE d nb) ⟨X.p, xm⟩ (blk d Y)) = _
    rw [strictT_eq]
    have hY : Y.wf = true := by
      have e : Y.p &&& Y.m = 0 := Nat.eq_of_beq_eq_true h
      unfold V.wf
      rw [e]
      rfl
    exact (rmKW_eq hd X (blk d Y) d
      (fun j _ => ⟨blk_wf d hY j, blk_p_lt d Y j, blk_m_lt d Y j⟩)).1

theorem unlane_size (d : Nat) (L : V) : (unlane d L).size = d := by
  unfold unlane
  rw [Array.size_ofFn]

theorem unlane_get {d : Nat} (L : V) {i : Nat} (hi : i < d) : (unlane d L)[i]! = blk d L i := by
  unfold unlane
  rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn]

theorem mul_unlane {d : Nat} (hd : 0 < d) (X Y : V) :
    mul d (unlane d X) (unlane d Y) = unlane d (mulLane d (spreadE d d) X Y) := by
  apply Array.ext
  · unfold mul
    rw [Array.size_map, unlane_size, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    have e1 := mul_getElem! (d := d) (X := unlane d X) (Y := unlane d Y)
      (by rw [unlane_size]; exact hi)
    rw [getElem!_pos _ i h1] at e1
    rw [e1, ← getElem!_pos (unlane d (mulLane d (spreadE d d) X Y)) i h2, unlane_get _ hi,
      unlane_get _ hi]
    rw [mulLane_eq hd, blk_rmK hd X (blk d Y) (fun j _ => ⟨blk_p_lt d Y j, blk_m_lt d Y j⟩) hi (unlane d Y)
      (fun j hj => unlane_get Y hj)]

theorem canonM_unlane (d : Nat) {L : V} (h : L.wf = true) : canonM d (unlane d L) = true := by
  unfold CFSG.F3.Native.canonM
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true]
  refine ⟨unlane_size d L, fun i hi => ?_⟩
  have hi' : i < d := by rwa [unlane_size] at hi
  have e : (unlane d L)[i] = blk d L i := by
    have := unlane_get (d := d) L hi'
    rwa [getElem!_pos _ i hi] at this
  rw [e]
  simp only [blk_wf d h i, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.div_eq_of_lt (blk_p_lt d L i), Nat.div_eq_of_lt (blk_m_lt d L i)]
  exact ⟨rfl, rfl⟩

noncomputable def dg (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

noncomputable def entsOf (cs : List Char) : List Nat :=
  (cs.filter fun c => !wsChar c).map dg

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beq_char (c d : Char) : (c == d) = (c.toNat == d.toNat) :=
  Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, beq_iff_eq]; exact Char.toNat_inj.symm)

theorem nbeq (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · exact (Bool.eq_false_iff.mpr fun e => by rw [beq_iff_eq] at e; subst e; simp at h).symm
  · rw [Nat.eq_of_beq_eq_true h]
    simp

theorem bIf_eq (c t e : Bool) :
    Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> cases t <;> cases e <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> cases b <;> rfl

theorem wsK_eq (c : Char) : wsK c.toNat = wsChar c := by
  unfold wsK wsChar
  simp only [bIf_eq, nbeq, beq_char]
  have e1 : (' ' : Char).toNat = 32 := rfl
  have e2 : ('\t' : Char).toNat = 9 := rfl
  have e3 : ('\n' : Char).toNat = 10 := rfl
  have e4 : ('\r' : Char).toNat = 13 := rfl
  rw [e1, e2, e3, e4]
  cases (c.toNat == 32) <;> cases (c.toNat == 9) <;> cases (c.toNat == 10) <;>
    cases (c.toNat == 13) <;> cases (c.toNat == 11) <;> cases (c.toNat == 12) <;> rfl

theorem entK_eq (c : Char) : entK c.toNat = dg c := by
  unfold entK dg
  have h1 : ('0' ≤ c) ↔ 48 ≤ c.toNat := by
    change ('0' : Char).val ≤ c.val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have h2 : (c ≤ '9') ↔ c.toNat ≤ 57 := by
    change c.val ≤ ('9' : Char).val ↔ _
    rw [UInt32.le_iff_toNat_le]
    rfl
  have e0 : ('0' : Char).toNat = 48 := rfl
  by_cases a : c.toNat < 48
  · have : Nat.blt c.toNat 48 = true := Nat.blt_eq.mpr a
    rw [this]
    have : ¬ ('0' ≤ c) := fun x => by rw [h1] at x; omega
    simp [this]
  · have : Nat.blt c.toNat 48 = false := by
      cases e : Nat.blt c.toNat 48
      · rfl
      · exact absurd (Nat.blt_eq.mp e) a
    rw [this]
    by_cases b : c.toNat < 58
    · have : Nat.blt c.toNat 58 = true := Nat.blt_eq.mpr b
      rw [this]
      have x1 : '0' ≤ c := by rw [h1]; omega
      have x2 : c ≤ '9' := by rw [h2]; omega
      simp [x1, x2, e0]
    · have : Nat.blt c.toNat 58 = false := by
        cases e : Nat.blt c.toNat 58
        · rfl
        · exact absurd (Nat.blt_eq.mp e) b
      rw [this]
      have x2 : ¬ c ≤ '9' := fun x => by rw [h2] at x; omega
      simp [x2]

theorem entOK_spec {L : V} {k e : Nat} (h : entOK L k e = true) :
    L.p.testBit k = decide (e % 3 = 1) ∧ L.m.testBit k = decide (e % 3 = 2) := by
  unfold entOK at h
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : Nat.mod e 3 = e % 3 := rfl
  rw [e1] at h1 h2
  constructor
  · cases hb : L.p.testBit k <;> rw [hb] at h1 <;> simp_all [nbeq]
  · cases hb : L.m.testBit k <;> rw [hb] at h2 <;> simp_all [nbeq]

theorem seedBody_spec {N : Nat} {L : V} : ∀ (cs : List Char) (k : Nat),
    seedBody N L cs k = true → N ≤ k + (entsOf cs).length ∧
      ∀ idx (hi : idx < (entsOf cs).length), k + idx < N → entOK L (k + idx) (entsOf cs)[idx] = true
  | [], k, h => by
    have : N ≤ k := Nat.le_of_ble_eq_true h
    exact ⟨by simpa [entsOf] using this, fun idx hi => absurd hi (by simp [entsOf])⟩
  | ch :: cs, k, h => by
    change strictB (Char.toNat ch) (fun c =>
      bIf(wsK c, seedBody N L cs k,
        bIf(Nat.blt k N, bAnd(entOK L k (entK c), seedBody N L cs (Nat.succ k)),
          seedBody N L cs (Nat.succ k)))) = true at h
    rw [strictB_eq', wsK_eq] at h
    cases hw : wsChar ch <;> rw [hw] at h
    · have e : entsOf (ch :: cs) = dg ch :: entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      cases hb : Nat.blt k N <;> rw [hb] at h
      · have hk : N ≤ k := by
          cases e2 : decide (k < N)
          · simpa using e2
          · rw [Nat.blt_eq.mpr (by simpa using e2)] at hb
            exact Bool.noConfusion hb
        obtain ⟨a, -⟩ := seedBody_spec cs (k + 1) h
        refine ⟨by simp; omega, fun idx hi hk' => absurd hk' (by omega)⟩
      · rw [bAnd_eq, Bool.and_eq_true] at h
        obtain ⟨a, b⟩ := seedBody_spec cs (k + 1) h.2
        refine ⟨by simp; omega, fun idx hi hk' => ?_⟩
        rcases idx with _ | idx
        · rw [← entK_eq]
          exact h.1
        · rw [List.getElem_cons_succ, show k + (idx + 1) = k + 1 + idx by omega]
          exact b idx (by simpa using hi) (by omega)
    · have e : entsOf (ch :: cs) = entsOf cs := by
        simp [entsOf, hw]
      rw [e]
      exact seedBody_spec cs k h

theorem seedHead_spec {N : Nat} {L : V} : ∀ cs : List Char, seedHead N L cs = true →
    seedBody N L ((cs.dropWhile (· != '\n')).drop 1) 0 = true
  | [], h => by
    change Nat.ble N 0 = true at h
    exact h
  | ch :: cs, h => by
    change Bool.rec (motive := fun _ => Bool) (seedHead N L cs) (seedBody N L cs 0)
      (Nat.beq (Char.toNat ch) 10) = true at h
    cases hb : Nat.beq (Char.toNat ch) 10 <;> rw [hb] at h
    · have hne : (ch != '\n') = true := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_pos (p := fun x => x != '\n') hne]
      exact seedHead_spec cs h
    · have hne : (ch != '\n') = false := by
        rw [bne, beq_char]
        have : ('\n' : Char).toNat = 10 := rfl
        rw [this, ← nbeq, hb]
        rfl
      rw [List.dropWhile_cons_of_neg (p := fun x => x != '\n') (by simp [hne])]
      exact h

theorem rowsOf_seed {d : Nat} {L : V} {cs : List Char} (h : seedK d L cs = true) :
    rowsOf d (String.ofList cs) = unlane d L := by
  obtain ⟨hlen, hent⟩ := seedBody_spec _ 0 (seedHead_spec cs h)
  have hdec : decodeEntries (String.ofList cs) = entsOf ((cs.dropWhile (· != '\n')).drop 1) := by
    unfold decodeEntries entsOf dg
    rw [String.toList_ofList]
  generalize entsOf ((cs.dropWhile (· != '\n')).drop 1) = E at hdec hlen hent
  change d * d ≤ 0 + E.length at hlen
  change ∀ idx (hi : idx < E.length), 0 + idx < d * d → entOK L (0 + idx) E[idx] = true at hent
  apply Array.ext
  · unfold rowsOf
    rw [Array.size_ofFn, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (unlane d L) i h2, unlane_get L hi]
    unfold rowsOf
    simp only [Array.getElem_ofFn, hdec]
    rw [ofFn_eq_fold]
    apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro j
    · rw [(fold_ofFnStep_bits _ j d).1, blk_p]
      by_cases hj : j < d
      · have hk : d * i + j < d * d := by
          have : d * i + j < d * (i + 1) := by rw [Nat.mul_succ]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ (by omega))
        have hidx : i * d + j < E.length := by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega
        have := (entOK_spec (hent (i * d + j) hidx (by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          change 0 + (i * d + j) < d * d
          omega))).1
        rw [Nat.zero_add] at this
        rw [show d * i + j = i * d + j by rw [Nat.mul_comm], this]
        simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray,
          List.getElem?_eq_getElem hidx, Option.getD_some]
      · simp [hj]
    · rw [(fold_ofFnStep_bits _ j d).2, blk_m]
      by_cases hj : j < d
      · have hk : d * i + j < d * d := by
          have : d * i + j < d * (i + 1) := by rw [Nat.mul_succ]; omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ (by omega))
        have hidx : i * d + j < E.length := by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          omega
        have := (entOK_spec (hent (i * d + j) hidx (by
          have : i * d + j = d * i + j := by rw [Nat.mul_comm]
          change 0 + (i * d + j) < d * d
          omega))).2
        rw [Nat.zero_add] at this
        rw [show d * i + j = i * d + j by rw [Nat.mul_comm], this]
        simp only [hj, decide_true, Bool.true_and, List.getElem?_toArray,
          List.getElem?_eq_getElem hidx, Option.getD_some]
      · simp [hj]

theorem eqM_self {d : Nat} {X : Array V} (h : X.size = d) : eqM d X X = true := by
  unfold eqM
  simp only [h, beq_self_eq_true, Bool.true_and]
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  intro i _
  simp [V.beq]

theorem unlane_inj {d : Nat} {X Y : V} (hXp : X.p < 2 ^ (d * d)) (hXm : X.m < 2 ^ (d * d))
    (hYp : Y.p < 2 ^ (d * d)) (hYm : Y.m < 2 ^ (d * d)) (h : unlane d X = unlane d Y) : X = Y := by
  have hb : ∀ k < d * d, (blk d X (k / d)) = (blk d Y (k / d)) := by
    intro k hk
    have hd : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hk
      · exact h
    have hkd : k / d < d := (Nat.div_lt_iff_lt_mul hd).2 hk
    rw [← unlane_get X hkd, ← unlane_get Y hkd, h]
  have hpos : ∀ k < d * d, d * (k / d) + k % d = k := fun k _ => Nat.div_add_mod k d
  have hmod : ∀ k < d * d, k % d < d := fun k hk => Nat.mod_lt _ (by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hk
    · exact h)
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · by_cases hk : k < d * d
    · have e1 := blk_p d X (k / d) (k % d)
      have e2 := blk_p d Y (k / d) (k % d)
      rw [hpos k hk, decide_eq_true (hmod k hk), Bool.true_and] at e1 e2
      rw [← e1, ← e2, hb k hk]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hXp (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hYp (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  · by_cases hk : k < d * d
    · have e1 := blk_m d X (k / d) (k % d)
      have e2 := blk_m d Y (k / d) (k % d)
      rw [hpos k hk, decide_eq_true (hmod k hk), Bool.true_and] at e1 e2
      rw [← e1, ← e2, hb k hk]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hXm (Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hYm (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem eqM_unlane {d : Nat} {X Y : V} (hX : X.wf = true) (hY : Y.wf = true)
    (hXp : X.p < 2 ^ (d * d)) (hXm : X.m < 2 ^ (d * d)) (hYp : Y.p < 2 ^ (d * d))
    (hYm : Y.m < 2 ^ (d * d)) (h : eqM d (unlane d X) (unlane d Y) = true) : X = Y :=
  unlane_inj hXp hXm hYp hYm (eq_of_canonM (canonM_unlane d hX) (canonM_unlane d hY)
    (toMat_eq_of_eqM h))

theorem powM_unlane {d : Nat} (hd : 0 < d) {I : V} (hI : idM d = unlane d I) (X : V) :
    ∀ e, powM d (unlane d X) e = unlane d (powLane d (spreadE d d) I X e)
  | 0 => hI
  | e + 1 => by
    rw [powM, powM_unlane hd hI X e, mul_unlane hd]
    rfl

end CFSG.KS.F3L

end
