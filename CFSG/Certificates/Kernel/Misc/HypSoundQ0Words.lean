module

public import Certificates.Data.Kernel.Misc.Hyp
public import CFSG.Certificates.Kernel.Misc.XiTab
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KC.Misc.Hyp

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73 CFSG.KS.PK
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi

private noncomputable def wst_q0 (TP : Nat → Nat) (QB PW : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
    (fun t acc => wordsK.step TP QB PW (t / 31) (t % 31) acc)

private noncomputable def wseen_q0 (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Nat :=
  wst_q0 TP QB PW t % 2 ^ 693

private noncomputable def wcntG (n : Nat) (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Nat :=
  wst_q0 TP QB PW t / 2 ^ n

private noncomputable def wcnt_q0 (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Nat :=
  wcntG 693 TP QB PW t

private theorem wordsK_notB_beq_zero_q0 (acc : Nat) (h0 : acc ≠ 0) :
    notB (acc.beq 0) = true := by
  cases hb : acc.beq 0
  · rfl
  · rw [Nat.beq_eq] at hb
    exact absurd hb h0

private theorem wordsK_step_zero_left_q0 (TP : Nat → Nat) (QB PW h k acc : Nat)
    (h0 : acc = 0) : wordsK.step TP QB PW h k acc = 0 := by
  unfold wordsK.step
  simp [letN_eq, h0]

private theorem wordsK_step_zero_ge_q0 (TP : Nat → Nat) (QB PW h k acc : Nat)
    (hlt : ¬ h < Nat.shiftRight acc 693) : wordsK.step TP QB PW h k acc = 0 := by
  unfold wordsK.step
  simp only [letN_eq]
  have hb : Nat.blt h (Nat.shiftRight acc 693) = false := by
    cases hh : Nat.blt h (Nat.shiftRight acc 693)
    · rfl
    · rw [Nat.blt_eq] at hh
      exact absurd hh hlt
  simp only [andB_eq, hb, Bool.and_false]

private theorem wordsK_step_eq_self_q0 (TP : Nat → Nat) (QB PW h k acc : Nat)
    (h0 : acc ≠ 0) (hlt : h < Nat.shiftRight acc 693)
    (hseen : bitK (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1))
      (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = true) :
    wordsK.step TP QB PW h k acc = acc := by
  unfold wordsK.step
  simp only [letN_eq]
  have hc0 := wordsK_notB_beq_zero_q0 acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hseen]

private theorem wordsK_step_eq_new_q0 (TP : Nat → Nat) (QB PW h k acc : Nat)
    (h0 : acc ≠ 0) (hlt : h < Nat.shiftRight acc 693)
    (hns : bitK (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1))
      (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = false)
    (hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight acc 693))
          (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
        (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
          (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))))) = true) :
    wordsK.step TP QB PW h k acc =
      Nat.add (Nat.lor (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1))
          (Nat.shiftLeft 1 (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h))))
        (Nat.shiftLeft (Nat.succ (Nat.shiftRight acc 693)) 693) := by
  unfold wordsK.step
  simp only [letN_eq]
  have hc0 := wordsK_notB_beq_zero_q0 acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hns, hchk]

private theorem wordsK_step_eq_zero_q0 (TP : Nat → Nat) (QB PW h k acc : Nat)
    (h0 : acc ≠ 0) (hlt : h < Nat.shiftRight acc 693)
    (hns : bitK (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1))
      (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = false)
    (hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight acc 693))
          (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
        (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
          (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))))) = false) :
    wordsK.step TP QB PW h k acc = 0 := by
  unfold wordsK.step
  simp only [letN_eq]
  have hc0 := wordsK_notB_beq_zero_q0 acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hns, hchk]

private theorem wrec_inner_q0 (TP : Nat → Nat) (QB PW h : Nat) :
    ∀ m ≤ 31, ∀ acc, acc = wst_q0 TP QB PW (31 * h) →
      Nat.rec (motive := fun _ => Nat) acc
        (fun k acc2 => wordsK.step TP QB PW h k acc2) m = wst_q0 TP QB PW (31 * h + m) := by
  intro m
  induction m with
  | zero => intro _ acc hacc; exact hacc
  | succ m ih =>
    intro hm acc hacc
    have hrec := ih (by omega) acc hacc
    have hstep : wordsK.step TP QB PW h m (wst_q0 TP QB PW (31 * h + m)) =
        wst_q0 TP QB PW (31 * h + (m + 1)) := by
      have e1 : (31 * h + m) / 31 = h := by omega
      have e2 : (31 * h + m) % 31 = m := by omega
      show wordsK.step TP QB PW h m (wst_q0 TP QB PW (31 * h + m)) =
        wordsK.step TP QB PW ((31 * h + m) / 31) ((31 * h + m) % 31)
          (wst_q0 TP QB PW (31 * h + m))
      rw [e1, e2]
    show wordsK.step TP QB PW h m (Nat.rec (motive := fun _ => Nat) acc
        (fun k acc2 => wordsK.step TP QB PW h k acc2) m) = _
    rw [hrec]
    exact hstep

private theorem wst_eq_replay_q0 (TP : Nat → Nat) (QB PW : Nat) :
    ∀ n, Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
        (fun h acc => Nat.rec (motive := fun _ => Nat) acc
          (fun k acc2 => wordsK.step TP QB PW h k acc2) 31) n = wst_q0 TP QB PW (31 * n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.rec (motive := fun _ => Nat)
        (Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
          (fun h acc => Nat.rec (motive := fun _ => Nat) acc
            (fun k acc2 => wordsK.step TP QB PW h k acc2) 31) n)
        (fun k acc2 => wordsK.step TP QB PW n k acc2) 31 = wst_q0 TP QB PW (31 * (n + 1))
    rw [ih]
    have h := wrec_inner_q0 TP QB PW n 31 (by omega) (wst_q0 TP QB PW (31 * n)) rfl
    rwa [show 31 * n + 31 = 31 * (n + 1) from by omega] at h

private theorem wst_zero_of_q0 {TP : Nat → Nat} {QB PW : Nat} {t : Nat}
    (h : wst_q0 TP QB PW t = 0) : ∀ n, wst_q0 TP QB PW (t + n) = 0 := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from by omega]
    rw [show wst_q0 TP QB PW ((t + n) + 1) =
        wordsK.step TP QB PW ((t + n) / 31) ((t + n) % 31) (wst_q0 TP QB PW (t + n)) from rfl]
    rw [ih]
    exact wordsK_step_zero_left_q0 TP QB PW ((t + n) / 31) ((t + n) % 31) 0 rfl

private theorem wst_ne_zero_q0 {TP : Nat → Nat} {QB PW : Nat}
    (h : wst_q0 TP QB PW (31 * 693) ≠ 0) :
    ∀ t ≤ 31 * 693, wst_q0 TP QB PW t ≠ 0 := by
  intro t ht h0
  have := wst_zero_of_q0 h0 (31 * 693 - t)
  rw [show t + (31 * 693 - t) = 31 * 693 from by omega] at this
  exact h this

private theorem shiftLeft_one_mul_q0 (n : Nat) : Nat.shiftLeft 1 n = 1 * 2 ^ n := by
  change (1 : Nat) <<< n = 1 * 2 ^ n
  rw [Nat.shiftLeft_eq]

private theorem shiftLeft_one_q0 (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := by
  rw [shiftLeft_one_mul_q0, Nat.one_mul]

private theorem shiftLeft_mul_q0 (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := by
  change a <<< b = a * 2 ^ b
  rw [Nat.shiftLeft_eq]

private theorem shiftRight_div_q0 (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := by
  change a >>> b = a / 2 ^ b
  rw [Nat.shiftRight_eq_div_pow]

private theorem land_maskG (x n : Nat) :
    Nat.land x (Nat.sub (Nat.shiftLeft 1 n) 1) = x % 2 ^ n := by
  rw [shiftLeft_one_q0 n]
  exact Nat.and_two_pow_sub_one_eq_mod x n

private theorem wcnt_shiftRightG (n : Nat) (TP : Nat → Nat) (QB PW t : Nat) :
    wcntG n TP QB PW t = Nat.shiftRight (wst_q0 TP QB PW t) n := by
  unfold wcntG
  exact (shiftRight_div_q0 (wst_q0 TP QB PW t) n).symm

private theorem wcnt_shiftRight_q0 (TP : Nat → Nat) (QB PW t : Nat) :
    wcnt_q0 TP QB PW t = Nat.shiftRight (wst_q0 TP QB PW t) 693 := by
  unfold wcnt_q0
  exact wcnt_shiftRightG 693 TP QB PW t

private theorem wseen_land_q0 (TP : Nat → Nat) (QB PW t : Nat) :
    wseen_q0 TP QB PW t = Nat.land (wst_q0 TP QB PW t) (Nat.sub (Nat.shiftLeft 1 693) 1) := by
  unfold wseen_q0
  exact (land_maskG (wst_q0 TP QB PW t) 693).symm

private theorem wst_zero_q0 (TP : Nat → Nat) (QB PW : Nat) :
    wst_q0 TP QB PW 0 = Nat.add 1 (Nat.shiftLeft 1 693) := rfl

private theorem lt_two_pow_of_pos_q0 {n : Nat} (hn : 0 < n) : (1 : Nat) < 2 ^ n := by
  have h := Nat.pow_lt_pow_right (by norm_num : (1 : Nat) < 2) hn
  rwa [pow_zero] at h

private theorem sub_one_shiftLeft_pos_q0 {n : Nat} (hn : 0 < n) :
    0 < Nat.sub (Nat.shiftLeft 1 n) 1 := by
  rw [shiftLeft_one_q0 n]
  exact Nat.pos_of_ne_zero (Nat.sub_ne_zero_of_lt (lt_two_pow_of_pos_q0 hn))

private theorem land_one_add_shiftLeftG {n : Nat} (hn : 0 < n) :
    Nat.land (Nat.add 1 (Nat.shiftLeft 1 n)) (Nat.sub (Nat.shiftLeft 1 n) 1) = 1 := by
  rw [land_maskG, shiftLeft_one_mul_q0 n]
  exact (Nat.add_mul_mod_self_right (1 : Nat) 1 (2 ^ n)).trans
    (Nat.mod_eq_of_lt (lt_two_pow_of_pos_q0 hn))

private theorem wseen_zero_q0 (TP : Nat → Nat) (QB PW : Nat) : wseen_q0 TP QB PW 0 = 1 := by
  rw [wseen_land_q0, wst_zero_q0]
  exact land_one_add_shiftLeftG (n := 693) (by norm_num)

private theorem wcntG_zero (n : Nat) (TP : Nat → Nat) (QB PW : Nat) (hn : 0 < n)
    (h : wst_q0 TP QB PW 0 = Nat.add 1 (Nat.shiftLeft 1 n)) :
    wcntG n TP QB PW 0 = 1 := by
  unfold wcntG
  rw [h, shiftLeft_one_mul_q0 n]
  have hh := Nat.add_mul_div_right (1 : Nat) 1 (Nat.two_pow_pos n)
  rw [Nat.div_eq_of_lt (lt_two_pow_of_pos_q0 hn), Nat.zero_add] at hh
  exact hh

private theorem wcnt_zero_q0 (TP : Nat → Nat) (QB PW : Nat) : wcnt_q0 TP QB PW 0 = 1 :=
  wcntG_zero 693 TP QB PW (by norm_num) (wst_zero_q0 TP QB PW)

private theorem wnew_lor_ltG {m st y : Nat} (hy : y < m) :
    Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 m) 1)) (Nat.shiftLeft 1 y) < 2 ^ m := by
  rw [land_maskG, shiftLeft_one_q0]
  exact Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos m))
    (Nat.pow_lt_pow_right (by norm_num) hy)

private theorem wnew_lor_lt_q0 {st y : Nat} (hy : y < 693) :
    Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) < 2 ^ 693 :=
  wnew_lor_ltG (m := 693) hy

private theorem land_add_shiftG {m a c : Nat} (ha : a < 2 ^ m) :
    Nat.land (Nat.add a (Nat.shiftLeft c m)) (Nat.sub (Nat.shiftLeft 1 m) 1) = a := by
  rw [land_maskG]
  rw [show Nat.shiftLeft c m = c * 2 ^ m from Nat.shiftLeft_eq c m]
  exact (Nat.add_mul_mod_self_right a c (2 ^ m)).trans (Nat.mod_eq_of_lt ha)

private theorem land_add_shift_q0 {a c : Nat} (ha : a < 2 ^ 693) :
    Nat.land (Nat.add a (Nat.shiftLeft c 693)) (Nat.sub (Nat.shiftLeft 1 693) 1) = a :=
  land_add_shiftG (m := 693) ha

private theorem wseen_new_testBit_q0 {TP : Nat → Nat} {QB PW p y i : Nat}
    (hy : y < 693)
    (hstn1 : wst_q0 TP QB PW (p + 1) =
      Nat.add (Nat.lor (Nat.land (wst_q0 TP QB PW p) (Nat.sub (Nat.shiftLeft 1 693) 1))
        (Nat.shiftLeft 1 y))
        (Nat.shiftLeft (Nat.succ (Nat.shiftRight (wst_q0 TP QB PW p) 693)) 693))
    (hiy : i ≠ y) :
    (wseen_q0 TP QB PW (p + 1)).testBit i = (wseen_q0 TP QB PW p).testBit i := by
  have hlor : Nat.lor (Nat.land (wst_q0 TP QB PW p) (Nat.sub (Nat.shiftLeft 1 693) 1))
      (Nat.shiftLeft 1 y) < 2 ^ 693 :=
    wnew_lor_lt_q0 (st := wst_q0 TP QB PW p) (y := y) hy
  rw [wseen_land_q0, hstn1]
  rw [land_add_shift_q0
    (a := Nat.lor (Nat.land (wst_q0 TP QB PW p) (Nat.sub (Nat.shiftLeft 1 693) 1))
      (Nat.shiftLeft 1 y))
    (c := Nat.succ (Nat.shiftRight (wst_q0 TP QB PW p) 693)) hlor]
  rw [Nat.lor_eq, Nat.testBit_lor,
    show Nat.shiftLeft 1 y = 2 ^ y from shiftLeft_one_q0 y, Nat.testBit_two_pow]
  rw [decide_eq_false (fun h : y = i => hiy h.symm), Bool.or_false]
  rw [wseen_land_q0]

private theorem wordsK_base_q0 {TP WT GI : Nat → Nat} {QB PW : Nat}
    (hw : wordsK TP WT GI QB PW = true) :
    WT 0 = idP 693 10 ∧
    (∀ x < 693, at' 10 (WT x) 0 = x ∧ permK 693 10 (GI x) = true ∧
      compP 693 10 (WT x) (GI x) = idP 693 10 ∧
      (x ≠ 0 → WT x = compP 693 10 (TP (at' 20 PW x / 1024))
        (WT (at' 20 PW x % 1024)))) := by
  have h := hw
  unfold wordsK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, allN_lqt_iff, letB_eq, impB_eq,
    notB_eq] at h
  obtain ⟨-, h2, h3⟩ := h
  refine ⟨h2, fun x hx => ?_⟩
  obtain ⟨h31, h32, h33, h34⟩ := h3 x hx
  refine ⟨h31, h32, h33, ?_⟩
  intro hx0
  rcases (Bool.or_eq_true_iff.mp h34) with hb | hb
  · exfalso
    have hb' : x = 0 := by simpa [Bool.not_not, Nat.beq_eq] using hb
    exact hx0 hb'
  · rwa [Nat.beq_eq] at hb

theorem qb0_of_words {TP WT GI : Nat → Nat} {QB PW : Nat}
    (hcover : ∀ z, 0 < z → z < 693 → ∃ k < 31, fd 10 (TP (23 * k)) z = z)
    (hmove : ∀ k < 31, ∃ p < 693, fd 10 (TP (23 * k)) p ≠ p)
    (hlt : ∀ k < 31, ∀ p, p < 693 → fd 10 (TP (23 * k)) p < 693)
    (hzero : ∀ k < 31, ∀ p, 693 ≤ p → p < 1024 → fd 10 (TP (23 * k)) p = 0)
    (hw : wordsK TP WT GI QB PW = true) : at' 10 QB 0 = 0 := by
  by_contra hne
  have hrep : wst_q0 TP QB PW (31 * 693) =
      Nat.add (Nat.sub (Nat.shiftLeft 1 693) 1) (Nat.shiftLeft 693 693) := by
    rw [← wst_eq_replay_q0 TP QB PW 693]
    have h := hw
    unfold wordsK at h
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    exact h.1
  have hfin : wst_q0 TP QB PW (31 * 693) ≠ 0 := by
    rw [hrep]
    have hM : 0 < Nat.sub (Nat.shiftLeft 1 693) 1 :=
      sub_one_shiftLeft_pos_q0 (n := 693) (by norm_num)
    exact (Nat.add_pos_left hM (Nat.shiftLeft 693 693)).ne'
  have hz1024 : at' 10 QB 0 < 1024 := by
    rw [CFSG.KS.PK.at'_eq]
    exact lt_of_lt_of_le (fd_lt 10 QB 0) (by norm_num)
  by_cases hzlt : at' 10 QB 0 < 693
  ·
    have hex : ∃ k, k < 31 ∧ fd 10 (TP (Nat.mul 23 k)) (at' 10 QB 0) = at' 10 QB 0 := by
      obtain ⟨k, hk, hkf⟩ := hcover (at' 10 QB 0) (Nat.pos_of_ne_zero hne) hzlt
      exact ⟨k, hk, hkf⟩
    let k0 := Nat.find hex
    have hk0spec : k0 < 31 ∧ fd 10 (TP (Nat.mul 23 k0)) (at' 10 QB 0) = at' 10 QB 0 :=
      Nat.find_spec hex
    have hk0lt : k0 < 31 := hk0spec.1
    have hk0fix : fd 10 (TP (Nat.mul 23 k0)) (at' 10 QB 0) = at' 10 QB 0 := hk0spec.2
    have hmin : ∀ t < k0, fd 10 (TP (Nat.mul 23 t)) (at' 10 QB 0) ≠ at' 10 QB 0 := by
      intro t ht hcon
      exact Nat.find_min hex ht ⟨by omega, hcon⟩
    have hseenbit : ∀ t, t ≤ k0 → (wseen_q0 TP QB PW t).testBit (at' 10 QB 0) = false := by
      intro t
      induction t with
      | zero =>
        intro _
        rw [wseen_zero_q0, show (1 : Nat) = 2 ^ 0 from by norm_num, Nat.testBit_two_pow]
        exact decide_eq_false (fun h : (0 : Nat) = at' 10 QB 0 => hne h.symm)
      | succ n ih =>
        intro hn
        have hnlt : n < k0 := by omega
        have hprev := ih (by omega)
        have hn31 : n < 31 := by omega
        have hpos : wst_q0 TP QB PW (n + 1) ≠ 0 := wst_ne_zero_q0 hfin (n + 1) (by omega)
        have hst0 : wst_q0 TP QB PW n ≠ 0 := wst_ne_zero_q0 hfin n (by omega)
        have hltc : n / 31 < Nat.shiftRight (wst_q0 TP QB PW n) 693 := by
          by_contra hg
          exact hpos (by
            rw [show wst_q0 TP QB PW (n + 1) =
              wordsK.step TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n) from rfl]
            exact wordsK_step_zero_ge_q0 TP QB PW (n / 31) (n % 31) _ hg)
        have hh : n / 31 = 0 := by omega
        have hk : n % 31 = n := by omega
        have hyne : fd 10 (TP (Nat.mul 23 n)) (at' 10 QB 0) ≠ at' 10 QB 0 := hmin n hnlt
        have hyz : at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))
            = fd 10 (TP (Nat.mul 23 n)) (at' 10 QB 0) := by
          rw [hh, hk]
          exact CFSG.KS.PK.at'_eq 10 (TP (Nat.mul 23 n)) (at' 10 QB 0)
        have hy_lt : at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31)) < 693 := by
          rw [hyz]
          exact hlt n hn31 (at' 10 QB 0) hzlt
        have hiy : at' 10 QB 0 ≠ at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31)) := by
          intro h
          rw [hyz] at h
          exact hyne h.symm
        by_cases hseen : bitK (Nat.land (wst_q0 TP QB PW n) (Nat.sub (Nat.shiftLeft 1 693) 1))
            (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))) = true
        · have hstep := wordsK_step_eq_self_q0 TP QB PW (n / 31) (n % 31)
            (wst_q0 TP QB PW n) hst0 hltc hseen
          have hstn1 : wst_q0 TP QB PW (n + 1) = wst_q0 TP QB PW n := by
            rw [show wst_q0 TP QB PW (n + 1) =
              wordsK.step TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n) from rfl, hstep]
          have heq : (wseen_q0 TP QB PW (n + 1)).testBit (at' 10 QB 0)
              = (wseen_q0 TP QB PW n).testBit (at' 10 QB 0) := by
            rw [wseen_land_q0, wseen_land_q0, hstn1]
          rw [heq, hprev]
        · have hns : bitK (Nat.land (wst_q0 TP QB PW n) (Nat.sub (Nat.shiftLeft 1 693) 1))
              (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))) = false := by
            cases hb : bitK (Nat.land (wst_q0 TP QB PW n) (Nat.sub (Nat.shiftLeft 1 693) 1))
                (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31)))
            · rfl
            · exact absurd hb hseen
          have hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight (wst_q0 TP QB PW n) 693))
                (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))))
              (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))))
                (Nat.add (at' 10 QB (n / 31)) (Nat.mul 1024 (Nat.mul 23 (n % 31)))))) = true := by
            cases hc : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight (wst_q0 TP QB PW n) 693))
                  (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))))
                (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))))
                  (Nat.add (at' 10 QB (n / 31)) (Nat.mul 1024 (Nat.mul 23 (n % 31))))))
            · exfalso
              exact hpos (by
                rw [show wst_q0 TP QB PW (n + 1) =
                  wordsK.step TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n) from rfl]
                exact wordsK_step_eq_zero_q0 TP QB PW (n / 31) (n % 31) _ hst0 hltc hns hc)
            · rfl
          have hstn1 : wst_q0 TP QB PW (n + 1) =
              Nat.add (Nat.lor (Nat.land (wst_q0 TP QB PW n) (Nat.sub (Nat.shiftLeft 1 693) 1))
                (Nat.shiftLeft 1 (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31)))))
                (Nat.shiftLeft (Nat.succ (Nat.shiftRight (wst_q0 TP QB PW n) 693)) 693) := by
            rw [show wst_q0 TP QB PW (n + 1) =
              wordsK.step TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n) from rfl]
            exact wordsK_step_eq_new_q0 TP QB PW (n / 31) (n % 31) _ hst0 hltc hns hchk
          exact (wseen_new_testBit_q0 (p := n) hy_lt hstn1 hiy).trans hprev
    have hseenk0 : (wseen_q0 TP QB PW k0).testBit (at' 10 QB 0) = false := hseenbit k0 (le_refl k0)
    have hst0k : wst_q0 TP QB PW k0 ≠ 0 := wst_ne_zero_q0 hfin k0 (by omega)
    have hposk : wst_q0 TP QB PW (k0 + 1) ≠ 0 := wst_ne_zero_q0 hfin (k0 + 1) (by omega)
    have hltck : k0 / 31 < Nat.shiftRight (wst_q0 TP QB PW k0) 693 := by
      by_contra hg
      exact hposk (by
        rw [show wst_q0 TP QB PW (k0 + 1) =
          wordsK.step TP QB PW (k0 / 31) (k0 % 31) (wst_q0 TP QB PW k0) from rfl]
        exact wordsK_step_zero_ge_q0 TP QB PW (k0 / 31) (k0 % 31) _ hg)
    have hh0 : k0 / 31 = 0 := by omega
    have hk0' : k0 % 31 = k0 := by omega
    have hy0 : at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31)) = at' 10 QB 0 := by
      rw [hh0, hk0']
      exact (CFSG.KS.PK.at'_eq 10 (TP (Nat.mul 23 k0)) (at' 10 QB 0)).trans hk0fix
    have hns0 : bitK (Nat.land (wst_q0 TP QB PW k0) (Nat.sub (Nat.shiftLeft 1 693) 1))
        (at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31))) = false := by
      rw [bitK_eq_testBit, ← wseen_land_q0, hy0]
      exact hseenk0
    have hchk0 : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight (wst_q0 TP QB PW k0) 693))
          (at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31))))
        (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31))))
          (Nat.add (at' 10 QB (k0 / 31)) (Nat.mul 1024 (Nat.mul 23 (k0 % 31)))))) = true := by
      cases hc : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight (wst_q0 TP QB PW k0) 693))
            (at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31))))
          (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 (k0 % 31))) (at' 10 QB (k0 / 31))))
            (Nat.add (at' 10 QB (k0 / 31)) (Nat.mul 1024 (Nat.mul 23 (k0 % 31))))))
      · exfalso
        exact hposk (by
          rw [show wst_q0 TP QB PW (k0 + 1) =
            wordsK.step TP QB PW (k0 / 31) (k0 % 31) (wst_q0 TP QB PW k0) from rfl]
          exact wordsK_step_eq_zero_q0 TP QB PW (k0 / 31) (k0 % 31) _ hst0k hltck hns0 hc)
      · rfl
    have hchk2 : at' 20 PW (at' 10 QB 0) =
        Nat.add (at' 10 QB 0) (Nat.mul 1024 (Nat.mul 23 k0)) := by
      have hh2 := (Bool.and_eq_true_iff.mp hchk0).2
      rw [Nat.beq_eq] at hh2
      rw [hy0, hh0, hk0'] at hh2
      exact hh2
    have hzbase := (wordsK_base_q0 hw).2 (at' 10 QB 0) hzlt
    have hWTz : WT (at' 10 QB 0) =
        compP 693 10 (TP (Nat.mul 23 k0)) (WT (at' 10 QB 0)) := by
      have h := hzbase.2.2.2 hne
      rw [hchk2] at h
      have hdiv2 : (Nat.add (at' 10 QB 0) (Nat.mul 1024 (Nat.mul 23 k0))) / 1024
          = Nat.mul 23 k0 := by
        have hd := Nat.add_mul_div_left (at' 10 QB 0) (Nat.mul 23 k0)
          (y := 1024) (by norm_num : 0 < 1024)
        rw [show at' 10 QB 0 / 1024 = 0 from Nat.div_eq_of_lt (by omega), Nat.zero_add] at hd
        simpa using hd
      have hmod2 : (Nat.add (at' 10 QB 0) (Nat.mul 1024 (Nat.mul 23 k0))) % 1024
          = at' 10 QB 0 := by
        have hm := Nat.add_mul_mod_self_left (at' 10 QB 0) (Nat.mul 23 k0) (y := 1024)
        rw [show at' 10 QB 0 % 1024 = at' 10 QB 0 from Nat.mod_eq_of_lt (by omega)] at hm
        simpa using hm
      rw [hdiv2, hmod2] at h
      exact h
    have hperm : IsPermN 693 (fd 10 (GI (at' 10 QB 0))) := (permK_iff.mp hzbase.2.1).2
    have hcomp : compP 693 10 (WT (at' 10 QB 0)) (GI (at' 10 QB 0)) = idP 693 10 :=
      hzbase.2.2.1
    have hfg : ∀ i < 693, fd 10 (WT (at' 10 QB 0)) (fd 10 (GI (at' 10 QB 0)) i) = i := by
      intro i hi
      have hi' := congrArg (fun w => fd 10 w i) hcomp
      rw [fd_compP _ _ hi, fd_idP hi] at hi'
      exact hi'
    have hsurjT : ∀ q < 693, ∃ p < 693, fd 10 (WT (at' 10 QB 0)) p = q := by
      intro q hq
      exact ⟨fd 10 (GI (at' 10 QB 0)) q, hperm.1 q hq, hfg q hq⟩
    have hfix : ∀ q < 693, fd 10 (TP (Nat.mul 23 k0)) q = q := by
      intro q hq
      obtain ⟨p, hp, hpq⟩ := hsurjT q hq
      have hc := congrArg (fun w => fd 10 w p) hWTz
      rw [fd_compP _ _ hp] at hc
      rw [hpq] at hc
      exact hc.symm
    obtain ⟨p, hp, hpm⟩ := hmove k0 hk0lt
    exact hpm (hfix p hp)
  ·
    have hzge : 693 ≤ at' 10 QB 0 := by omega
    have hy : ∀ t < 31, at' 10 (TP (Nat.mul 23 t)) (at' 10 QB 0) = 0 := by
      intro t ht
      exact (CFSG.KS.PK.at'_eq 10 (TP (Nat.mul 23 t)) (at' 10 QB 0)).trans
        (hzero t ht (at' 10 QB 0) hzge hz1024)
    have hstt : ∀ t, t ≤ 31 → wst_q0 TP QB PW t = wst_q0 TP QB PW 0 := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have hn31 : n < 31 := by omega
        have hprev := ih (by omega)
        have hst0 : wst_q0 TP QB PW n ≠ 0 := wst_ne_zero_q0 hfin n (by omega)
        have hcnt : Nat.shiftRight (wst_q0 TP QB PW n) 693 = 1 := by
          rw [← wcnt_shiftRight_q0]
          have hwe : wcnt_q0 TP QB PW n = wcnt_q0 TP QB PW 0 := by
            rw [wcnt_shiftRight_q0, wcnt_shiftRight_q0, hprev]
          rw [hwe, wcnt_zero_q0]
        have hh : n / 31 = 0 := by omega
        have hk : n % 31 = n := by omega
        have hltc : n / 31 < Nat.shiftRight (wst_q0 TP QB PW n) 693 := by
          rw [hcnt, hh]
          omega
        have hseen : bitK (Nat.land (wst_q0 TP QB PW n) (Nat.sub (Nat.shiftLeft 1 693) 1))
            (at' 10 (TP (Nat.mul 23 (n % 31))) (at' 10 QB (n / 31))) = true := by
          rw [hh, hk, bitK_eq_testBit, ← wseen_land_q0, hy n hn31]
          have hwe : wseen_q0 TP QB PW n = wseen_q0 TP QB PW 0 := by
            rw [wseen_land_q0, wseen_land_q0, hprev]
          rw [hwe, wseen_zero_q0, show (1 : Nat) = 2 ^ 0 from by norm_num, Nat.testBit_two_pow]
          exact decide_eq_true rfl
        have hstep := wordsK_step_eq_self_q0 TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n)
          hst0 hltc hseen
        rw [show wst_q0 TP QB PW (n + 1) =
            wordsK.step TP QB PW (n / 31) (n % 31) (wst_q0 TP QB PW n) from rfl, hstep, hprev]
    have hst31 : wst_q0 TP QB PW 31 = wst_q0 TP QB PW 0 := hstt 31 (le_refl 31)
    have hcnt31 : Nat.shiftRight (wst_q0 TP QB PW 31) 693 = 1 := by
      rw [← wcnt_shiftRight_q0]
      have hwe : wcnt_q0 TP QB PW 31 = wcnt_q0 TP QB PW 0 := by
        rw [wcnt_shiftRight_q0, wcnt_shiftRight_q0, hst31]
      rw [hwe, wcnt_zero_q0]
    have hge : ¬ (1 : Nat) < Nat.shiftRight (wst_q0 TP QB PW 31) 693 := by
      rw [hcnt31]
      omega
    have hstep31 : wst_q0 TP QB PW 32 = 0 := by
      rw [show wst_q0 TP QB PW 32 =
          wordsK.step TP QB PW (31 / 31) (31 % 31) (wst_q0 TP QB PW 31) from rfl,
        show (31 : Nat) / 31 = 1 from by norm_num,
        show (31 : Nat) % 31 = 0 from by norm_num]
      exact wordsK_step_zero_ge_q0 TP QB PW 1 0 (wst_q0 TP QB PW 31) hge
    exact wst_ne_zero_q0 hfin 32 (by norm_num) hstep31

end CFSG.KC.Misc.Hyp

end
