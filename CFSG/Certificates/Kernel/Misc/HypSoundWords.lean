module

public import CFSG.Certificates.Kernel.Misc.HypNative
public import Certificates.Data.Kernel.Misc.Hyp

public section

set_option exponentiation.threshold 10000

namespace CFSG.KC.Misc.Hyp

open CFSG.F4.Native CFSG.Sporadic.Th.Native CFSG.Fischer.Native CFSG.KC.Misc.T46
  CFSG.KC.Misc.Lines CFSG.KC.Misc.Xi CFSG.KS.PK CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc
  CFSG.KC.Misc.O73 CFSG.KS.TW

private noncomputable def wst (TP : Nat → Nat) (QB PW : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
    (fun t acc => wordsK.step TP QB PW (t / 31) (t % 31) acc)

private noncomputable def wseen (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Nat :=
  wst TP QB PW t % 2 ^ 693

private noncomputable def wcnt (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Nat :=
  wst TP QB PW t / 2 ^ 693

private theorem wordsK_notB_beq_zero (acc : Nat) (h0 : acc ≠ 0) : notB (acc.beq 0) = true := by
  cases hb : acc.beq 0
  · rfl
  · rw [Nat.beq_eq] at hb
    exact absurd hb h0

private theorem wordsK_step_zero_left (TP : Nat → Nat) (QB PW h k acc : Nat) (h0 : acc = 0) :
    wordsK.step TP QB PW h k acc = 0 := by
  unfold wordsK.step
  simp [letN_eq, h0]

private theorem wordsK_step_zero_ge (TP : Nat → Nat) (QB PW h k acc : Nat)
    (hlt : ¬ h < Nat.shiftRight acc 693) :
    wordsK.step TP QB PW h k acc = 0 := by
  unfold wordsK.step
  simp only [letN_eq]
  have hb : Nat.blt h (Nat.shiftRight acc 693) = false := by
    cases hh : Nat.blt h (Nat.shiftRight acc 693)
    · rfl
    · rw [Nat.blt_eq] at hh
      exact absurd hh hlt
  simp only [andB_eq, hb, Bool.and_false]

private theorem wordsK_step_eq_self (TP : Nat → Nat) (QB PW h k acc : Nat)
    (h0 : acc ≠ 0) (hlt : h < Nat.shiftRight acc 693)
    (hseen : bitK (Nat.land acc (Nat.sub (Nat.shiftLeft 1 693) 1))
      (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = true) :
    wordsK.step TP QB PW h k acc = acc := by
  unfold wordsK.step
  simp only [letN_eq]
  have hc0 := wordsK_notB_beq_zero acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hseen]

private theorem wordsK_step_eq_new (TP : Nat → Nat) (QB PW h k acc : Nat)
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
  have hc0 := wordsK_notB_beq_zero acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hns, hchk]

private theorem wordsK_step_eq_zero (TP : Nat → Nat) (QB PW h k acc : Nat)
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
  have hc0 := wordsK_notB_beq_zero acc h0
  have hc1 : Nat.blt h (Nat.shiftRight acc 693) = true := by rw [Nat.blt_eq]; exact hlt
  simp only [andB_eq, hc0, hc1, Bool.true_and, hns, hchk]

private theorem wrec_inner (TP : Nat → Nat) (QB PW h : Nat) :
    ∀ m ≤ 31, ∀ acc, acc = wst TP QB PW (31 * h) →
      Nat.rec (motive := fun _ => Nat) acc
        (fun k acc2 => wordsK.step TP QB PW h k acc2) m = wst TP QB PW (31 * h + m) := by
  intro m
  induction m with
  | zero => intro _ acc hacc; exact hacc
  | succ m ih =>
    intro hm acc hacc
    have hrec := ih (by omega) acc hacc
    have hstep : wordsK.step TP QB PW h m (wst TP QB PW (31 * h + m)) =
        wst TP QB PW (31 * h + (m + 1)) := by
      have e1 : (31 * h + m) / 31 = h := by omega
      have e2 : (31 * h + m) % 31 = m := by omega
      show wordsK.step TP QB PW h m (wst TP QB PW (31 * h + m)) =
        wordsK.step TP QB PW ((31 * h + m) / 31) ((31 * h + m) % 31)
          (wst TP QB PW (31 * h + m))
      rw [e1, e2]
    show wordsK.step TP QB PW h m (Nat.rec (motive := fun _ => Nat) acc
        (fun k acc2 => wordsK.step TP QB PW h k acc2) m) = _
    rw [hrec]
    exact hstep

private theorem wst_eq_replay (TP : Nat → Nat) (QB PW : Nat) :
    ∀ n, Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
        (fun h acc => Nat.rec (motive := fun _ => Nat) acc
          (fun k acc2 => wordsK.step TP QB PW h k acc2) 31) n = wst TP QB PW (31 * n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show Nat.rec (motive := fun _ => Nat)
        (Nat.rec (motive := fun _ => Nat) (Nat.add 1 (Nat.shiftLeft 1 693))
          (fun h acc => Nat.rec (motive := fun _ => Nat) acc
            (fun k acc2 => wordsK.step TP QB PW h k acc2) 31) n)
        (fun k acc2 => wordsK.step TP QB PW n k acc2) 31 = wst TP QB PW (31 * (n + 1))
    rw [ih]
    have h := wrec_inner TP QB PW n 31 (by omega) (wst TP QB PW (31 * n)) rfl
    rwa [show 31 * n + 31 = 31 * (n + 1) from by omega] at h

private theorem wst_zero_of {TP : Nat → Nat} {QB PW : Nat} {t : Nat}
    (h : wst TP QB PW t = 0) : ∀ n, wst TP QB PW (t + n) = 0 := by
  intro n
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 from by omega]
    rw [show wst TP QB PW ((t + n) + 1) =
        wordsK.step TP QB PW ((t + n) / 31) ((t + n) % 31) (wst TP QB PW (t + n)) from rfl]
    rw [ih]
    exact wordsK_step_zero_left TP QB PW ((t + n) / 31) ((t + n) % 31) 0 rfl

private theorem wst_ne_zero {TP : Nat → Nat} {QB PW : Nat}
    (h : wst TP QB PW (31 * 693) ≠ 0) :
    ∀ t ≤ 31 * 693, wst TP QB PW t ≠ 0 := by
  intro t ht h0
  have := wst_zero_of h0 (31 * 693 - t)
  rw [show t + (31 * 693 - t) = 31 * 693 from by omega] at this
  exact h this

private theorem shiftLeft_one (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := by
  have h : Nat.shiftLeft 1 n = 1 * 2 ^ n := by
    change (1 : Nat) <<< n = 1 * 2 ^ n
    rw [Nat.shiftLeft_eq]
  rwa [Nat.one_mul] at h

private theorem shiftLeft_mul (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := by
  change a <<< b = a * 2 ^ b
  rw [Nat.shiftLeft_eq]

private theorem shiftRight_div (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := by
  change a >>> b = a / 2 ^ b
  rw [Nat.shiftRight_eq_div_pow]

private theorem land_mask (x : Nat) :
    Nat.land x (Nat.sub (Nat.shiftLeft 1 693) 1) = x % 2 ^ 693 := by
  rw [shiftLeft_one]
  exact Nat.and_two_pow_sub_one_eq_mod x 693

private theorem wcnt_shiftRight (TP : Nat → Nat) (QB PW t : Nat) :
    wcnt TP QB PW t = Nat.shiftRight (wst TP QB PW t) 693 := by
  unfold wcnt
  exact (shiftRight_div (wst TP QB PW t) 693).symm

private theorem wseen_land (TP : Nat → Nat) (QB PW t : Nat) :
    wseen TP QB PW t = Nat.land (wst TP QB PW t) (Nat.sub (Nat.shiftLeft 1 693) 1) := by
  unfold wseen
  exact (land_mask (wst TP QB PW t)).symm

private theorem wst_zero (TP : Nat → Nat) (QB PW : Nat) :
    wst TP QB PW 0 = Nat.add 1 (Nat.shiftLeft 1 693) := rfl

private theorem wseen_zero (TP : Nat → Nat) (QB PW : Nat) : wseen TP QB PW 0 = 1 := by
  unfold wseen
  rw [wst_zero, shiftLeft_one]
  show (1 + 1 * 2 ^ 693) % 2 ^ 693 = 1
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 693)]

private theorem wcnt_zero (TP : Nat → Nat) (QB PW : Nat) : wcnt TP QB PW 0 = 1 := by
  unfold wcnt
  rw [wst_zero, shiftLeft_one]
  show (1 + 1 * 2 ^ 693) / 2 ^ 693 = 1
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 693),
    Nat.div_eq_of_lt (by norm_num : 1 < 2 ^ 693), Nat.zero_add]

private structure WInv (TP : Nat → Nat) (QB PW : Nat) (t : Nat) : Prop where
  qlt : ∀ c < wcnt TP QB PW t, fd 10 QB c < 693
  q0 : fd 10 QB 0 = 0
  inj : ∀ c < wcnt TP QB PW t, ∀ c' < wcnt TP QB PW t,
    fd 10 QB c = fd 10 QB c' → c = c'
  mem : ∀ y < 693, (wseen TP QB PW t).testBit y = true ↔
    ∃ c < wcnt TP QB PW t, fd 10 QB c = y
  tree : ∀ c, 0 < c → c < wcnt TP QB PW t →
    ∃ h < c, ∃ k < 31, fd 10 QB c = fd 10 (TP (Nat.mul 23 k)) (fd 10 QB h) ∧
      at' 20 PW (fd 10 QB c) = Nat.add (fd 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))

private theorem winv_zero {TP : Nat → Nat} {QB PW : Nat} (hq0 : at' 10 QB 0 = 0) :
    WInv TP QB PW 0 := by
  have hq : fd 10 QB 0 = 0 := by rw [← at'_eq]; exact hq0
  refine ⟨?_, hq, ?_, ?_, ?_⟩
  · intro c hc
    rw [wcnt_zero] at hc
    have : c = 0 := by omega
    subst this
    omega
  · intro c hc c' hc' _
    rw [wcnt_zero] at hc hc'
    omega
  · intro y hy
    rw [wseen_zero]
    have hbit : (1 : Nat).testBit y = decide (y = 0) := by
      rw [show (1 : Nat) = 2 ^ 0 from by norm_num, Nat.testBit_two_pow]
      exact decide_eq_decide.2 eq_comm
    rw [hbit]
    constructor
    · intro h
      refine ⟨0, by rw [wcnt_zero]; omega, ?_⟩
      rw [hq]
      exact (of_decide_eq_true h).symm
    · rintro ⟨c, hc, hcq⟩
      rw [wcnt_zero] at hc
      have : c = 0 := by omega
      subst this
      rw [hq] at hcq
      exact decide_eq_true hcq.symm
  · intro c hc0 hc
    rw [wcnt_zero] at hc
    omega

private theorem wnew_lor_lt {st y : Nat} (hy : y < 693) :
    Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) < 2 ^ 693 := by
  rw [land_mask]
  exact Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos 693))
    (by rw [shiftLeft_one]; exact Nat.pow_lt_pow_right (by norm_num) hy)

private theorem wnew_cnt {st y : Nat}
    (h : Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) < 2 ^ 693) :
    (Nat.add (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
        (Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693)) / 2 ^ 693
      = Nat.succ (Nat.shiftRight st 693) := by
  rw [show Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693
      = (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693 from shiftLeft_mul _ _]
  have hd : ((Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
      + (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693) / 2 ^ 693
      = Nat.succ (Nat.shiftRight st 693) := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 693), Nat.div_eq_of_lt h, Nat.zero_add]
  exact hd

private theorem wnew_seen {st y : Nat}
    (h : Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) < 2 ^ 693) :
    (Nat.add (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
        (Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693)) % 2 ^ 693
      = Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) := by
  rw [show Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693
      = (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693 from shiftLeft_mul _ _]
  have hm : ((Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
      + (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693) % 2 ^ 693
      = Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]
  exact hm

private theorem winv_step {U : Array Nat} {TP : Nat → Nat} {QB PW : Nat} {t : Nat}
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hI : WInv TP QB PW t) (hpos : wst TP QB PW (t + 1) ≠ 0) :
    WInv TP QB PW (t + 1) := by
  set st := wst TP QB PW t with hst
  set h := t / 31 with hh
  set k := t % 31 with hk
  have hstep : wst TP QB PW (t + 1) = wordsK.step TP QB PW h k st := by
    rw [hst]; rfl
  have hst0 : st ≠ 0 := by
    intro h0
    exact hpos (by rw [hstep]; exact wordsK_step_zero_left TP QB PW h k st h0)
  have hlt : h < Nat.shiftRight st 693 := by
    by_contra hge
    exact hpos (by rw [hstep]; exact wordsK_step_zero_ge TP QB PW h k st hge)
  have hklt : k < 31 := by rw [hk]; exact Nat.mod_lt _ (by norm_num)
  have hcntst : wcnt TP QB PW t = Nat.shiftRight st 693 := by
    rw [wcnt_shiftRight, ← hst]
  set y := at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h) with hy
  by_cases hseen : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y = true
  · have hst' : wst TP QB PW (t + 1) = st := by
      rw [hstep]
      exact wordsK_step_eq_self TP QB PW h k st hst0 hlt (hy ▸ hseen)
    have hcE : wcnt TP QB PW (t + 1) = wcnt TP QB PW t := by unfold wcnt; rw [hst']
    have hsE : wseen TP QB PW (t + 1) = wseen TP QB PW t := by unfold wseen; rw [hst']
    refine ⟨?_, hI.q0, ?_, ?_, ?_⟩
    · intro c hc; rw [hcE] at hc; exact hI.qlt c hc
    · intro c hc c' hc' heq
      rw [hcE] at hc hc'; exact hI.inj c hc c' hc' heq
    · intro y' hy'; rw [hsE, hcE]; exact hI.mem y' hy'
    · intro c hc0 hc; rw [hcE] at hc; exact hI.tree c hc0 hc
  · have hns : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y = false := by
      cases hb : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y
      · rfl
      · exact absurd hb hseen
    have hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight st 693)) y)
        (Nat.beq (at' 20 PW y)
          (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))))) = true := by
      cases hc : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight st 693)) y)
          (Nat.beq (at' 20 PW y)
            (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k)))))
      · exfalso
        exact hpos (by rw [hstep]; exact
          wordsK_step_eq_zero TP QB PW h k st hst0 hlt (hy ▸ hns) (hy ▸ hc))
      · rfl
    have hst' : wst TP QB PW (t + 1) =
        Nat.add (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
          (Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693) := by
      rw [hstep]
      exact wordsK_step_eq_new TP QB PW h k st hst0 hlt (hy ▸ hns) (hy ▸ hchk)
    have hchk1 : at' 10 QB (Nat.shiftRight st 693) = y := by
      have hh := (Bool.and_eq_true_iff.mp hchk).1
      rwa [Nat.beq_eq] at hh
    have hchk2 : at' 20 PW y =
        Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k)) := by
      have hh := (Bool.and_eq_true_iff.mp hchk).2
      rwa [Nat.beq_eq] at hh
    have hcntpt : fd 10 QB (Nat.shiftRight st 693) = y := by rw [← at'_eq, hchk1]
    have hy_lt : y < 693 := by
      rw [hy, at'_eq, at'_eq]
      have hh : h < wcnt TP QB PW t := by rw [hcntst]; exact hlt
      have hk30 : k ≤ 30 := by omega
      have hm : Nat.mul 23 k < 693 := by
        calc Nat.mul 23 k ≤ Nat.mul 23 30 := Nat.mul_le_mul_left 23 hk30
          _ = 690 := by norm_num
          _ < 693 := by norm_num
      exact ((hTR (Nat.mul 23 k) hm).2 (fd 10 QB h) (hI.qlt h hh)).2
    have hlor := wnew_lor_lt (st := st) (y := y) hy_lt
    have hcnt' : wcnt TP QB PW (t + 1) = Nat.succ (Nat.shiftRight st 693) := by
      unfold wcnt
      rw [hst', wnew_cnt hlor]
    have hseen' : wseen TP QB PW (t + 1) =
        Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y) := by
      unfold wseen
      rw [hst', wnew_seen hlor]
    refine ⟨?_, hI.q0, ?_, ?_, ?_⟩
    · intro c hc
      rw [hcnt'] at hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hI.qlt c (by simpa [hcntst] using hc)
      · rw [hcntpt]; exact hy_lt
    · intro c hc c' hc' heq
      rw [hcnt'] at hc hc'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with hc' | rfl
      · exact hI.inj c (by simpa [hcntst] using hc) c' (by simpa [hcntst] using hc') heq
      · exfalso
        have hc1 : fd 10 QB c = y := by rw [heq, hcntpt]
        have hcb : c < wcnt TP QB PW t := by simpa [hcntst] using hc
        have hmem := (hI.mem y hy_lt).2 ⟨c, hcb, hc1⟩
        have hfl : (wseen TP QB PW t).testBit y = false := by
          rw [wseen_land, ← bitK_eq_testBit]; exact hns
        rw [hfl] at hmem
        exact Bool.noConfusion hmem
      · exfalso
        have hc1 : fd 10 QB c' = y := by rw [← heq, hcntpt]
        have hcb : c' < wcnt TP QB PW t := by simpa [hcntst] using hc'
        have hmem := (hI.mem y hy_lt).2 ⟨c', hcb, hc1⟩
        have hfl : (wseen TP QB PW t).testBit y = false := by
          rw [wseen_land, ← bitK_eq_testBit]; exact hns
        rw [hfl] at hmem
        exact Bool.noConfusion hmem
      · rfl
    · intro z hz
      rw [hseen', Nat.lor_eq, Nat.testBit_lor,
        show Nat.shiftLeft 1 y = 2 ^ y from shiftLeft_one y, Nat.testBit_two_pow,
        Bool.or_eq_true]
      have hmaskz : (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)).testBit z
          = (wseen TP QB PW t).testBit z := by rw [wseen_land]
      constructor
      · rintro (h | h)
        · obtain ⟨c, hc, hcq⟩ := (hI.mem z hz).1 (by rwa [hmaskz] at h)
          refine ⟨c, ?_, hcq⟩
          rw [hcnt']
          exact Nat.lt_succ_of_lt (by simpa [hcntst] using hc)
        · refine ⟨Nat.shiftRight st 693, ?_, ?_⟩
          · rw [hcnt']; exact Nat.lt_succ_self _
          · rw [hcntpt, of_decide_eq_true h]
      · rintro ⟨c, hc, hcq⟩
        rw [hcnt'] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · left
          have hcb : c < wcnt TP QB PW t := by simpa [hcntst] using hc
          have hm := (hI.mem z hz).2 ⟨c, hcb, hcq⟩
          rwa [hmaskz]
        · right
          have hzy : y = z := by rw [← hcntpt, hcq]
          exact decide_eq_true hzy
    · intro c hc0 hc
      rw [hcnt'] at hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact hI.tree c hc0 (by simpa [hcntst] using hc)
      · refine ⟨h, hlt, k, hklt, ?_, ?_⟩
        · rw [hcntpt]; rw [hy, at'_eq, at'_eq]
        · rw [hcntpt, hchk2, at'_eq]

private theorem wordsK_base {TP WT GI : Nat → Nat} {QB PW : Nat}
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

private theorem wcnt_final {TP : Nat → Nat} {QB PW : Nat}
    (h : wst TP QB PW (31 * 693) =
      Nat.add (Nat.sub (Nat.shiftLeft 1 693) 1) (Nat.shiftLeft 693 693)) :
    wcnt TP QB PW (31 * 693) = 693 := by
  unfold wcnt
  rw [h, show Nat.shiftLeft 693 693 = 693 * 2 ^ 693 from shiftLeft_mul _ _]
  have hd : (((Nat.sub (Nat.shiftLeft 1 693) 1) + 693 * 2 ^ 693) / 2 ^ 693) = 693 := by
    have hsub : (2 ^ 693).sub 1 < 2 ^ 693 :=
      Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num : 0 < 1)
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 693),
      show Nat.shiftLeft 1 693 = 2 ^ 693 from shiftLeft_one 693,
      Nat.div_eq_of_lt hsub, Nat.zero_add]
  exact hd

private theorem wseen_final {TP : Nat → Nat} {QB PW : Nat}
    (h : wst TP QB PW (31 * 693) =
      Nat.add (Nat.sub (Nat.shiftLeft 1 693) 1) (Nat.shiftLeft 693 693)) :
    wseen TP QB PW (31 * 693) = Nat.sub (Nat.shiftLeft 1 693) 1 := by
  unfold wseen
  rw [h, show Nat.shiftLeft 693 693 = 693 * 2 ^ 693 from shiftLeft_mul _ _]
  have hlt : Nat.sub (Nat.shiftLeft 1 693) 1 < 2 ^ 693 := by
    rw [shiftLeft_one]
    exact Nat.sub_lt (Nat.two_pow_pos 693) (by norm_num : 0 < 1)
  have hmod : (((Nat.sub (Nat.shiftLeft 1 693) 1) + 693 * 2 ^ 693) % 2 ^ 693)
      = Nat.sub (Nat.shiftLeft 1 693) 1 := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
  exact hmod

private theorem winv_all {U : Array Nat} {TP : Nat → Nat} {QB PW : Nat}
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hfin : wst TP QB PW (31 * 693) ≠ 0) (hq0 : at' 10 QB 0 = 0) :
    ∀ t ≤ 31 * 693, WInv TP QB PW t := by
  have h : ∀ t, t ≤ 31 * 693 → WInv TP QB PW t := by
    intro t
    induction t with
    | zero => intro _; exact winv_zero hq0
    | succ t ih =>
      intro ht
      exact winv_step hTR (ih (by omega)) (wst_ne_zero hfin (t + 1) ht)
  exact h

private theorem winv_final_mem {TP : Nat → Nat} {QB PW : Nat}
    (hI : WInv TP QB PW (31 * 693))
    (hseen : wseen TP QB PW (31 * 693) = Nat.sub (Nat.shiftLeft 1 693) 1)
    {x : Nat} (hx : x < 693) :
    ∃ c < wcnt TP QB PW (31 * 693), fd 10 QB c = x := by
  have hbit : (wseen TP QB PW (31 * 693)).testBit x = true := by
    rw [hseen, shiftLeft_one]
    change ((2 ^ 693 : Nat) - 1).testBit x = true
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
    exact hx
  exact (hI.mem x hx).1 hbit

private abbrev WSt := Array (List Nat) × Array Bool × Array Nat

private def gInit : WSt :=
  (Array.replicate 693 [], (Array.replicate 693 false).set! 0 true, #[0])

private def gInner (T : Array Table) (x : Nat) (k : Nat) (st : WSt) : Id (ForInStep WSt) :=
  let p := Nat.mul 23 k
  let y := ap T[p]! x
  if (!st.2.1[y]!) = true then
    pure (ForInStep.yield (st.1.set! y (p :: st.1[x]!), st.2.1.set! y true, st.2.2.push y))
  else pure (ForInStep.yield st)

private def gBody (T : Array Table) (h : Nat) (st : WSt) : Id (ForInStep WSt) :=
  if h < st.2.2.size then
    pure (ForInStep.yield (forIn (β := WSt) [:31] st (gInner T st.2.2[h]!)))
  else pure (ForInStep.done st)

private def gWordsT (T : Array Table) : Array (List Nat) := Id.run do
  let mut w : Array (List Nat) := Array.replicate 693 []
  let mut seen : Array Bool := (Array.replicate 693 false).set! 0 true
  let mut queue : Array Nat := #[0]
  for h in [0:693] do
    if h < queue.size then
      let x := queue[h]!
      for k in [0:31] do
        let p := 23 * k
        let y := ap T[p]! x
        if !seen[y]! then
          seen := seen.set! y true
          w := w.set! y (p :: w[x]!)
          queue := queue.push y
    else break
  return w

private theorem gWordsG_T (U : Array Nat) : gWordsG U = gWordsT (tvTabsG U) := rfl

private theorem gWordsT_eq (T : Array Table) :
    gWordsT T = (forIn [:693] (gInit) (gBody T)).1 := by
  unfold gWordsT gInit gBody gInner
  simp only [Id.run]
  rfl

private theorem gWordsG_eq (U : Array Nat) :
    gWordsG U = (forIn [:693] (gInit) (gBody (tvTabsG U))).1 :=
  (gWordsG_T U).trans (gWordsT_eq _)

private theorem TR_congr {n : Nat} {T : Table} {f g : Nat → Nat}
    (h : ∀ i < n, f i = g i) (hT : TR n T f) : TR n T g := by
  obtain ⟨hsz, hv⟩ := hT
  exact ⟨hsz, fun i hi => ⟨(hv i hi).1.trans (h i hi), by rw [← h i hi]; exact (hv i hi).2⟩⟩

private theorem fd_compP {A B : Nat} {i : Nat} (hi : i < 693) :
    fd 10 (compP 693 10 A B) i = fd 10 A (fd 10 B i) := by
  rw [compP_eq]
  exact fd_enc (fun i _ => fd_lt 10 A (fd 10 B i)) hi

private theorem fd_idP {i : Nat} (hi : i < 693) : fd 10 (idP 693 10) i = i := by
  rw [idP_eq (by norm_num : (693 : Nat) ≤ 2 ^ 10)]
  exact fd_enc (fun i hi => Nat.lt_of_lt_of_le hi (by norm_num : (693 : Nat) ≤ 2 ^ 10)) hi

private theorem tvWordTabG_cons (U : Array Nat) (p : Nat) (l : List Nat) :
    tvWordTabG U (p :: l) = compT 693 (tvTabsG U)[p]! (tvWordTabG U l) := by
  unfold tvWordTabG
  rw [List.foldr_cons]

private structure NInv (U : Array Nat) (TP WT : Nat → Nat) (QB PW : Nat) (t : Nat)
    (st : WSt) : Prop where
  wsize : st.1.size = 693
  ssize : st.2.1.size = 693
  qsize : st.2.2.size = wcnt TP QB PW t
  qget : ∀ c < wcnt TP QB PW t, st.2.2[c]! = fd 10 QB c
  seen : ∀ y < 693, st.2.1[y]! = (wseen TP QB PW t).testBit y
  wall : ∀ x < 693, (st.1[x]!).all (fun p => p < 693) = true
  wtr : ∀ c < wcnt TP QB PW t,
    TR 693 (tvWordTabG U (st.1[fd 10 QB c]!)) (fd 10 (WT (fd 10 QB c)))

private theorem wcnt_gt {TP : Nat → Nat} {QB PW : Nat}
    (hfin : wst TP QB PW (31 * 693) ≠ 0) {h : Nat} (hh : h < 693) :
    h < wcnt TP QB PW (31 * h) := by
  have hpos := wst_ne_zero hfin (31 * h + 1) (by omega)
  by_contra hge
  have hlt : ¬ h < Nat.shiftRight (wst TP QB PW (31 * h)) 693 := by
    intro hc
    exact hge (by rw [wcnt_shiftRight]; exact hc)
  exact hpos (by
    rw [show 31 * h + 1 = (31 * h) + 1 from by omega,
      show wst TP QB PW ((31 * h) + 1) = wordsK.step TP QB PW ((31 * h) / 31)
        ((31 * h) % 31) (wst TP QB PW (31 * h)) from rfl,
      show (31 * h) / 31 = h from by omega, show (31 * h) % 31 = 0 from by omega]
    exact wordsK_step_zero_ge TP QB PW h 0 _ hlt)

set_option maxRecDepth 100000 in
private theorem ninv_init {U : Array Nat} {TP WT : Nat → Nat} {QB PW : Nat}
    (hWT : WT 0 = idP 693 10) (hq0 : at' 10 QB 0 = 0) :
    NInv U TP WT QB PW 0 gInit := by
  have hq : fd 10 QB 0 = 0 := by rw [← at'_eq]; exact hq0
  have hbit : ∀ y < 693, (1 : Nat).testBit y = (if y = 0 then true else false) := by
    intro y hy
    rw [show (1 : Nat) = 2 ^ 0 from by norm_num, Nat.testBit_two_pow]
    by_cases hy0 : y = 0
    · rw [if_pos hy0, decide_eq_true hy0.symm]
    · rw [if_neg hy0, decide_eq_false (fun h : 0 = y => hy0 h.symm)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gInit, Array.size_replicate]
  · simp only [gInit, Array.size_set!, Array.size_replicate]
  · show (#[0] : Array Nat).size = wcnt TP QB PW 0
    rw [wcnt_zero]; rfl
  · intro c hc
    rw [wcnt_zero] at hc
    have hc0 : c = 0 := by omega
    subst hc0
    show (#[0] : Array Nat)[0]! = fd 10 QB 0
    rw [hq]; rfl
  · intro y hy
    rw [wseen_zero]
    have hset : gInit.2.1[y]! = (if y = 0 then true else false) := by
      have hg : gInit.2.1 = (Array.replicate 693 false).set! 0 true := rfl
      rw [hg]
      by_cases hy0 : y = 0
      · subst hy0
        rw [Array.getElem!_set!_self _ _ _ (by simp)]
        rfl
      · rw [Array.getElem!_set!_ne _ _ _ _ (fun h : 0 = y => hy0 h.symm)]
        rw [getElem!_pos _ y (by simp [hy]), Array.getElem_replicate]
        simp [hy0]
    rw [hset, hbit y hy]
  · intro x hx
    have hx0 : (Array.replicate 693 ([] : List Nat))[x]! = [] := by
      rw [getElem!_pos _ x (by simp [hx]), Array.getElem_replicate]
    show ((Array.replicate 693 ([] : List Nat))[x]!).all (fun p => p < 693) = true
    rw [hx0]
    rfl
  · intro c hc
    rw [wcnt_zero] at hc
    have hc0 : c = 0 := by omega
    subst hc0
    have hw : gInit.1[fd 10 QB 0]! = ([] : List Nat) := by
      have hg : gInit.1 = Array.replicate 693 ([] : List Nat) := rfl
      rw [hg, hq, getElem!_pos _ 0 (by simp), Array.getElem_replicate]
    rw [hw, hq, hWT]
    change TR 693 (idT 693) (fd 10 (idP 693 10))
    exact TR_congr (fun i hi => (fd_idP hi).symm) (idT_TR (by norm_num : 693 < 2 ^ 32))

private theorem wcnt_mono {TP : Nat → Nat} {QB PW t : Nat}
    (hpos : wst TP QB PW (t + 1) ≠ 0) :
    wcnt TP QB PW t ≤ wcnt TP QB PW (t + 1) := by
  set st := wst TP QB PW t with hst
  set h := t / 31 with hh
  set k := t % 31 with hk
  have hstep : wst TP QB PW (t + 1) = wordsK.step TP QB PW h k st := by rw [hst]; rfl
  have hst0 : st ≠ 0 := by
    intro h0; exact hpos (by rw [hstep]; exact wordsK_step_zero_left TP QB PW h k st h0)
  have hlt : h < Nat.shiftRight st 693 := by
    by_contra hge
    exact hpos (by rw [hstep]; exact wordsK_step_zero_ge TP QB PW h k st hge)
  set y := at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h) with hy
  have hcnt : wcnt TP QB PW t = Nat.shiftRight st 693 := by rw [wcnt_shiftRight, ← hst]
  by_cases hseen : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y = true
  · have hst' : wst TP QB PW (t + 1) = st := by
      rw [hstep]; exact wordsK_step_eq_self TP QB PW h k st hst0 hlt (hy ▸ hseen)
    rw [show wcnt TP QB PW (t + 1) = wcnt TP QB PW t from by unfold wcnt; rw [hst']]
  · have hns : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y = false := by
      cases hb : bitK (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) y
      · rfl
      · exact absurd hb hseen
    have hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight st 693)) y)
        (Nat.beq (at' 20 PW y)
          (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))))) = true := by
      cases hc : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight st 693)) y)
          (Nat.beq (at' 20 PW y)
            (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k)))))
      · exfalso
        exact hpos (by rw [hstep]; exact
          wordsK_step_eq_zero TP QB PW h k st hst0 hlt (hy ▸ hns) (hy ▸ hc))
      · rfl
    have hst' : wst TP QB PW (t + 1) =
        Nat.add (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
          (Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693) := by
      rw [hstep]; exact wordsK_step_eq_new TP QB PW h k st hst0 hlt (hy ▸ hns) (hy ▸ hchk)
    have hnew : wcnt TP QB PW (t + 1) =
        (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y)) / 2 ^ 693
          + Nat.succ (Nat.shiftRight st 693) := by
      unfold wcnt
      rw [hst', show Nat.shiftLeft (Nat.succ (Nat.shiftRight st 693)) 693
          = (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693 from shiftLeft_mul _ _]
      have hd : ((Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y))
          + (Nat.succ (Nat.shiftRight st 693)) * 2 ^ 693) / 2 ^ 693
          = (Nat.lor (Nat.land st (Nat.sub (Nat.shiftLeft 1 693) 1)) (Nat.shiftLeft 1 y)) / 2 ^ 693
            + Nat.succ (Nat.shiftRight st 693) := by
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 693)]
      exact hd
    rw [hnew, hcnt]
    omega

private theorem ninv_inner {U : Array Nat} {TP WT GI : Nat → Nat} {QB PW : Nat}
    (hw : wordsK TP WT GI QB PW = true)
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hfin : wst TP QB PW (31 * 693) ≠ 0)
    {h k : Nat} (h_lt : h < 693) (hk : k < 31) {x : Nat} (hx : x = fd 10 QB h)
    (hh : h < wcnt TP QB PW (31 * h + k))
    (hI : WInv TP QB PW (31 * h + k))
    {ns : WSt} (hN : NInv U TP WT QB PW (31 * h + k) ns) :
    ∃ ns', gInner (tvTabsG U) x k ns = pure (ForInStep.yield ns') ∧
      NInv U TP WT QB PW (31 * h + (k + 1)) ns' := by
  have hk693 : Nat.mul 23 k < 693 := by
    have hk30 : k ≤ 30 := by omega
    calc Nat.mul 23 k ≤ Nat.mul 23 30 := Nat.mul_le_mul_left 23 hk30
      _ = 690 := by norm_num
      _ < 693 := by norm_num
  have hxlt : x < 693 := by rw [hx]; exact hI.qlt h hh
  generalize hK : wst TP QB PW (31 * h + k) = K
  generalize hy : ap (tvTabsG U)[Nat.mul 23 k]! x = y
  have hyfd : y = fd 10 (TP (Nat.mul 23 k)) x := by
    rw [← hy]; exact ((hTR (Nat.mul 23 k) hk693).2 x hxlt).1
  have hyk : y = at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h) := by
    rw [hyfd, at'_eq, at'_eq, hx]
  have hy_lt : y < 693 := by
    rw [hyfd, hx]
    exact ((hTR (Nat.mul 23 k) hk693).2 (fd 10 QB h) (hI.qlt h hh)).2
  have hdiv : (31 * h + k) / 31 = h := by omega
  have hmod : (31 * h + k) % 31 = k := by omega
  have hstep : wst TP QB PW (31 * h + (k + 1)) =
      wordsK.step TP QB PW h k K := by
    rw [show 31 * h + (k + 1) = (31 * h + k) + 1 from by omega,
      show wst TP QB PW ((31 * h + k) + 1) = wordsK.step TP QB PW
        ((31 * h + k) / 31) ((31 * h + k) % 31) (wst TP QB PW (31 * h + k)) from rfl,
      hdiv, hmod, hK]
  have hpos : wst TP QB PW (31 * h + (k + 1)) ≠ 0 := wst_ne_zero hfin _ (by omega)
  have hst0 : K ≠ 0 := by
    intro h0
    exact hpos (hstep.trans (wordsK_step_zero_left TP QB PW h k K h0))
  have hlt : h < Nat.shiftRight K 693 := by
    by_contra hge
    exact hpos (hstep.trans (wordsK_step_zero_ge TP QB PW h k K hge))
  have hcnst : wcnt TP QB PW (31 * h + k) = Nat.shiftRight K 693 := by
    rw [wcnt_shiftRight, hK]
  by_cases hseens : ns.2.1[y]! = true
  · have hseenw : (wseen TP QB PW (31 * h + k)).testBit y = true := by
      rw [← hN.seen y hy_lt, hseens]
    have hseenK : bitK (Nat.land (K)
        (Nat.sub (Nat.shiftLeft 1 693) 1)) (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = true := by
      rw [bitK_eq_testBit, ← hK, ← wseen_land, ← hyk]; exact hseenw
    have hst' : wst TP QB PW (31 * h + (k + 1)) = K :=
      hstep.trans (wordsK_step_eq_self TP QB PW h k K hst0 hlt hseenK)
    have hcE : wcnt TP QB PW (31 * h + (k + 1)) = wcnt TP QB PW (31 * h + k) := by
      unfold wcnt; rw [hst', hK]
    have hsE : wseen TP QB PW (31 * h + (k + 1)) = wseen TP QB PW (31 * h + k) := by
      unfold wseen; rw [hst', hK]
    have hgi : gInner (tvTabsG U) x k ns = pure (ForInStep.yield ns) := by
      unfold gInner
      rw [if_neg (by rw [hy]; simp [hseens])]
    refine ⟨ns, hgi, ?_⟩
    refine ⟨hN.wsize, hN.ssize, ?_, ?_, ?_, hN.wall, ?_⟩
    · rw [hcE]; exact hN.qsize
    · intro c hc; rw [hcE] at hc; exact hN.qget c hc
    · intro z hz; rw [hsE]; exact hN.seen z hz
    · intro c hc; rw [hcE] at hc; exact hN.wtr c hc
  · have hnsseen : ns.2.1[y]! = false := by
      cases hb : ns.2.1[y]!
      · rfl
      · exact absurd hb hseens
    have hseenw : (wseen TP QB PW (31 * h + k)).testBit y = false := by
      rw [← hN.seen y hy_lt, hnsseen]
    have hnsK : bitK (Nat.land (K)
        (Nat.sub (Nat.shiftLeft 1 693) 1)) (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)) = false := by
      rw [bitK_eq_testBit, ← hK, ← wseen_land, ← hyk]; exact hseenw
    have hchk : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight K 693))
          (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
        (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
          (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))))) = true := by
      cases hc : (Bool.and (Nat.beq (at' 10 QB (Nat.shiftRight K 693))
            (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
          (Nat.beq (at' 20 PW (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h)))
            (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k)))))
      · exfalso
        exact hpos (hstep.trans
          (wordsK_step_eq_zero TP QB PW h k K hst0 hlt hnsK hc))
      · rfl
    have hst' : wst TP QB PW (31 * h + (k + 1)) =
        Nat.add (Nat.lor (Nat.land K (Nat.sub (Nat.shiftLeft 1 693) 1))
            (Nat.shiftLeft 1 (at' 10 (TP (Nat.mul 23 k)) (at' 10 QB h))))
          (Nat.shiftLeft (Nat.succ (Nat.shiftRight K 693)) 693) :=
      hstep.trans (wordsK_step_eq_new TP QB PW h k K hst0 hlt hnsK hchk)
    have hchk1 : at' 10 QB (Nat.shiftRight K 693) = y := by
      have hh := (Bool.and_eq_true_iff.mp hchk).1
      rwa [Nat.beq_eq, ← hyk] at hh
    have hchk2 : at' 20 PW y =
        Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k)) := by
      have hh := (Bool.and_eq_true_iff.mp hchk).2
      rwa [Nat.beq_eq, ← hyk] at hh
    have hcntpt : fd 10 QB (Nat.shiftRight (K) 693) = y := by
      rw [← at'_eq, hchk1]
    have hwtstep : WT y = compP 693 10 (TP (Nat.mul 23 k)) (WT x) := by
      have hr := (wordsK_base hw).2 y hy_lt |>.2.2.2
      have hy0 : y ≠ 0 := by
        intro e
        have h0 : (wseen TP QB PW (31 * h + k)).testBit 0 = true :=
          (hI.mem 0 (by norm_num)).2 ⟨0, by rw [hcnst]; omega, hI.q0⟩
        rw [e] at hseenw
        rw [hseenw] at h0
        exact Bool.noConfusion h0
      have hrec := hr hy0
      rw [hchk2] at hrec
      have hdiv2 : (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))) / 1024
          = Nat.mul 23 k := by
        have hd := Nat.add_mul_div_left (at' 10 QB h) (Nat.mul 23 k)
          (y := 1024) (by norm_num : 0 < 1024)
        rw [show at' 10 QB h / 1024 = 0 from by
          rw [at'_eq]; exact Nat.div_eq_of_lt (by omega), Nat.zero_add] at hd
        simpa using hd
      have hmod2 : (Nat.add (at' 10 QB h) (Nat.mul 1024 (Nat.mul 23 k))) % 1024
          = fd 10 QB h := by
        have hm := Nat.add_mul_mod_self_left (at' 10 QB h) (Nat.mul 23 k) (y := 1024)
        rw [show at' 10 QB h % 1024 = fd 10 QB h from by
          rw [at'_eq]; exact Nat.mod_eq_of_lt (by omega)] at hm
        simpa using hm
      rw [hdiv2, hmod2] at hrec
      rw [← hx] at hrec
      exact hrec
    have hlor := wnew_lor_lt (st := K) (y := y) hy_lt
    have hct' : wcnt TP QB PW (31 * h + (k + 1))
        = Nat.succ (Nat.shiftRight (K) 693) := by
      unfold wcnt; rw [hst', hyk.symm, wnew_cnt hlor]
    have hse' : wseen TP QB PW (31 * h + (k + 1)) =
        Nat.lor (Nat.land (K) (Nat.sub (Nat.shiftLeft 1 693) 1))
          (Nat.shiftLeft 1 y) := by
      unfold wseen; rw [hst', hyk.symm, wnew_seen hlor]
    let ns' : WSt := (ns.1.set! y (Nat.mul 23 k :: ns.1[x]!), ns.2.1.set! y true, ns.2.2.push y)
    have hgi : gInner (tvTabsG U) x k ns = pure (ForInStep.yield ns') := by
      unfold gInner
      rw [if_pos (by rw [hy]; simp [hnsseen])]
      rw [hy]
    refine ⟨ns', hgi, ?_⟩
    have hbits : ∀ z < 693, (wseen TP QB PW (31 * h + (k + 1))).testBit z =
        (if z = y then true else (wseen TP QB PW (31 * h + k)).testBit z) := by
      intro z hz
      rw [hse', Nat.lor_eq, Nat.testBit_lor,
        show Nat.shiftLeft 1 y = 2 ^ y from shiftLeft_one y, Nat.testBit_two_pow]
      by_cases hzy : z = y
      · rw [if_pos hzy, decide_eq_true hzy.symm, Bool.or_true]
      · rw [if_neg hzy, decide_eq_false (fun h : y = z => hzy h.symm), Bool.or_false,
          ← hK, wseen_land]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Array.size_set!, hN.wsize]
    · rw [Array.size_set!, hN.ssize]
    · rw [Array.size_push, hct', hN.qsize, hcnst]
    · intro c hc
      rw [hct'] at hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · rw [push_getElem!_lt _ _ (by rw [hN.qsize, hcnst]; exact hc)]
        exact hN.qget c (by rwa [hcnst])
      · have hsz : ns.2.2.size = Nat.shiftRight (K) 693 := by
          rw [hN.qsize, hcnst]
        rw [← hsz, push_getElem!_size, hsz]
        exact hcntpt.symm
    · intro z hz
      rw [hbits z hz]
      by_cases hzy : z = y
      · rw [if_pos hzy, hzy]
        rw [Array.getElem!_set!_self _ _ _ (by rw [hN.ssize]; exact hy_lt)]
      · rw [if_neg hzy, Array.getElem!_set!_ne _ _ _ _ (fun h : y = z => hzy h.symm), hN.seen z hz]
    · intro z hz
      by_cases hzy : z = y
      · rw [hzy]
        have hnsy : ns'.1[y]! = Nat.mul 23 k :: ns.1[x]! :=
          Array.getElem!_set!_self ns.1 y (Nat.mul 23 k :: ns.1[x]!)
            (by rw [hN.wsize]; exact hy_lt)
        rw [hnsy, List.all_cons, Bool.and_eq_true]
        exact ⟨by simpa using hk693, hN.wall x hxlt⟩
      · have hne : y ≠ z := fun h => hzy h.symm
        rw [show ns'.1[z]! = ns.1[z]! from
          Array.getElem!_set!_ne _ _ _ _ hne]
        exact hN.wall z hz
    · intro c hc
      rw [hct'] at hc
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · have hcw : c < wcnt TP QB PW (31 * h + k) := by rwa [hcnst]
        have hne : y ≠ fd 10 QB c := by
          intro h
          have hmem := (hI.mem y hy_lt).2 ⟨c, hcw, h.symm⟩
          rw [wseen_land, hK, hyk, ← bitK_eq_testBit, hnsK] at hmem
          exact Bool.noConfusion hmem
        rw [show ns'.1[fd 10 QB c]! = ns.1[fd 10 QB c]! from
          Array.getElem!_set!_ne _ _ _ _ hne]
        exact hN.wtr c hcw
      · have htrx := hN.wtr h hh
        rw [← hx] at htrx
        have hnsy : ns'.1[y]! = Nat.mul 23 k :: ns.1[x]! :=
          Array.getElem!_set!_self ns.1 y (Nat.mul 23 k :: ns.1[x]!)
            (by rw [hN.wsize]; exact hy_lt)
        rw [hcntpt, hnsy, hwtstep]
        rw [tvWordTabG_cons]
        exact TR_congr (fun i hi => (fd_compP hi).symm)
          (compT_TR (by norm_num : 693 < 2 ^ 32) (hTR (Nat.mul 23 k) hk693) htrx)

private theorem ninv_outer {U : Array Nat} {TP WT GI : Nat → Nat} {QB PW : Nat}
    (hw : wordsK TP WT GI QB PW = true)
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hfin : wst TP QB PW (31 * 693) ≠ 0)
    (hWT : WT 0 = idP 693 10) (hq0 : at' 10 QB 0 = 0) :
    NInv U TP WT QB PW (31 * 693) (forIn (β := WSt) [:693] gInit (gBody (tvTabsG U))) := by
  refine CFSG.KC.J4Q.BfsOrder.forIn_range_inv (β := WSt)
    (I := fun h ns => NInv U TP WT QB PW (31 * h) ns)
    (Q := fun ns => NInv U TP WT QB PW (31 * 693) ns)
    (f := gBody (tvTabsG U)) (n := 693) (b := gInit) ?_ ?_ ?_
  · intro h ns hh hI
    have hh' : h < wcnt TP QB PW (31 * h) := wcnt_gt hfin hh
    have hlt : h < ns.2.2.size := hI.qsize.symm ▸ hh'
    have hget : ns.2.2[h]! = fd 10 QB h := hI.qget h hh'
    unfold gBody
    rw [if_pos hlt, hget]
    have hinner : NInv U TP WT QB PW (31 * h + 31)
          (forIn (β := WSt) [:31] ns (gInner (tvTabsG U) (fd 10 QB h)))
        ∧ h < wcnt TP QB PW (31 * h + 31) := by
      refine CFSG.KC.J4Q.BfsOrder.forIn_range_inv (β := WSt)
        (I := fun k ns' => NInv U TP WT QB PW (31 * h + k) ns' ∧ h < wcnt TP QB PW (31 * h + k))
        (Q := fun ns' => NInv U TP WT QB PW (31 * h + 31) ns' ∧ h < wcnt TP QB PW (31 * h + 31))
        (f := gInner (tvTabsG U) (fd 10 QB h)) (n := 31) (b := ns) ?_ ?_ ?_
      · intro k ns' hk hI'
        obtain ⟨hN', hhk'⟩ := hI'
        have hI0 : WInv TP QB PW (31 * h + k) := winv_all hTR hfin hq0 _ (by omega)
        have hwpos : wst TP QB PW (31 * h + k + 1) ≠ 0 := wst_ne_zero hfin _ (by omega)
        obtain ⟨ns'', hgi, hN''⟩ := ninv_inner hw hTR hfin hh hk rfl hhk' hI0 hN'
        rw [hgi]
        refine ⟨hN'', ?_⟩
        have hmono := wcnt_mono (t := 31 * h + k) hwpos
        have : wcnt TP QB PW (31 * h + k) ≤ wcnt TP QB PW (31 * h + (k + 1)) := by
          simpa [show 31 * h + k + 1 = 31 * h + (k + 1) from by omega] using hmono
        omega
      · intro ns' hI'; exact hI'
      · exact ⟨by simpa using hI, by simpa using hh'⟩
    change NInv U TP WT QB PW (31 * (h + 1))
      (forIn (β := WSt) [:31] ns (gInner (tvTabsG U) (fd 10 QB h)))
    have h1 := hinner.1
    rw [show 31 * (h + 1) = 31 * h + 31 from by omega]
    exact h1
  · intro ns hI; exact hI
  · exact ninv_init hWT hq0

theorem words_sound {U : Array Nat} {QB PW : Nat} {TP WT GI : Nat → Nat}
    (hTR : ∀ f < 693, TR 693 ((tvTabsG U)[f]!) (fd 10 (TP f)))
    (hw : wordsK TP WT GI QB PW = true) (hq0 : at' 10 QB 0 = 0) :
    wordsOKG U (gWordsG U) (wordInvsG U (gWordsG U)) = true ∧
      ∀ x < 693, TR 693 ((wordInvsG U (gWordsG U))[x]!) (fd 10 (GI x)) := by
  have hbase := wordsK_base hw
  have hrep : wst TP QB PW (31 * 693)
      = Nat.add (Nat.sub (Nat.shiftLeft 1 693) 1) (Nat.shiftLeft 693 693) := by
    rw [← wst_eq_replay TP QB PW 693]
    have h := hw
    unfold wordsK at h
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    exact h.1
  have hfin : wst TP QB PW (31 * 693) ≠ 0 := by
    rw [hrep]
    have hsl : 0 < Nat.shiftLeft 693 693 := by
      rw [shiftLeft_mul]; exact Nat.mul_pos (by norm_num) (Nat.two_pow_pos 693)
    exact (Nat.lt_of_lt_of_le hsl (Nat.le_add_left _ _)).ne'
  have hI : WInv TP QB PW (31 * 693) := winv_all hTR hfin hq0 (31 * 693) (le_refl _)
  have hseen := wseen_final (TP := TP) (QB := QB) (PW := PW) hrep
  have hcnt := wcnt_final (TP := TP) (QB := QB) (PW := PW) hrep
  have hN : NInv U TP WT QB PW (31 * 693) (forIn (β := WSt) [:693] gInit (gBody (tvTabsG U))) :=
    ninv_outer hw hTR hfin hbase.1 hq0
  have hres : gWordsG U = (forIn (β := WSt) [:693] gInit (gBody (tvTabsG U))).1 :=
    gWordsG_eq U
  have hgie : ∀ x < 693, (wordInvsG U (gWordsG U))[x]!
      = invT 693 (tvWordTabG U ((gWordsG U)[x]!)) := by
    intro x hx
    unfold wordInvsG
    rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn (h := by simpa using hx)]
  have hP : ∀ x < 693, TR 693 (tvWordTabG U ((gWordsG U)[x]!)) (fd 10 (WT x)) := by
    intro x hx
    obtain ⟨c, hc, hcq⟩ := winv_final_mem hI hseen hx
    have htr := hN.wtr c hc
    rw [← hcq, hres]
    exact htr
  have hR : ∀ x < 693, TR 693 ((wordInvsG U (gWordsG U))[x]!) (fd 10 (GI x)) := by
    intro x hx
    have hcomp := (hbase.2 x hx).2.2.1
    have hperm := (permK_iff.mp (hbase.2 x hx).2.1).2
    have hfg : ∀ i < 693, fd 10 (WT x) (fd 10 (GI x) i) = i := by
      intro i hi
      have hi' := congrArg (fun z => fd 10 z i) hcomp
      rw [fd_compP hi, fd_idP hi] at hi'
      exact hi'
    have hgf : ∀ i < 693, fd 10 (GI x) (fd 10 (WT x) i) = i := by
      intro i hi
      obtain ⟨j, hj, hji⟩ := hperm.surj (y := i) hi
      rw [← hji, hfg j hj]
    rw [hgie x hx]
    exact invT_TR (by norm_num : 693 < 2 ^ 32) (hP x hx)
      (fun i hi => ⟨hperm.1 i hi, hfg i hi, hgf i hi⟩)
  refine ⟨?_, hR⟩
  unfold wordsOKG
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hres, hN.wsize, beq_self_eq_true]
  · unfold wordInvsG; simp [Array.size_ofFn]
  · rw [allIn_iff]
    intro x hx
    simp only [Bool.and_eq_true, and_assoc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hres]; exact hN.wall x hx
    · have h0 := (hP x hx).2 0 (by norm_num)
      have hx0 : fd 10 (WT x) 0 = x := by rw [← at'_eq]; exact (hbase.2 x hx).1
      rw [h0.1, hx0, beq_self_eq_true]
    · have hcomp := (hbase.2 x hx).2.2.1
      have hfg : ∀ i < 693, fd 10 (WT x) (fd 10 (GI x) i) = i := by
        intro i hi
        have hi' := congrArg (fun z => fd 10 z i) hcomp
        rw [fd_compP hi, fd_idP hi] at hi'
        exact hi'
      have hgf : ∀ i < 693, fd 10 (GI x) (fd 10 (WT x) i) = i := by
        have hperm := (permK_iff.mp (hbase.2 x hx).2.1).2
        intro i hi
        obtain ⟨j, hj, hji⟩ := hperm.surj (y := i) hi
        rw [← hji, hfg j hj]
      rw [hgie x hx]
      have hRx := hR x hx
      rw [hgie x hx] at hRx
      exact invOK_of (hP x hx) hRx hgf

end CFSG.KC.Misc.Hyp

end
