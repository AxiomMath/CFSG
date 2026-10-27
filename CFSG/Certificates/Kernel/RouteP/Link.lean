module

public import CFSG.Certificates.Kernel.RouteP.MonoSound

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net CFSG.KC.KDense.SortAux

theorem allBelow_spec' {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; exact absurd hl (Nat.not_lt_zero l)
    | succ n ih =>
      intro hn l hl hlm
      obtain ⟨h1, h2⟩ := andB_true hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hl) with hl | rfl
      · exact ih h2 l hl hlm
      · have hc : Nat.blt (Nat.add (Nat.shiftLeft hh 6) l) m = true := Nat.blt_eq.mpr hlm
        beta_reduce at h1
        rw [hc] at h1
        exact h1
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; exact absurd hhh (Nat.not_lt_zero hh)
    | succ n ih =>
      intro hn hh hhh l hl hlm
      obtain ⟨h1, h2⟩ := andB_true hn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hhh) with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by decide)) (by rw [e]; exact him)
  rwa [e] at this

theorem testBit_blk' (P c : Nat) {r : Nat} (hr : r < 512) :
    (CFSG.KC.Fi24Net.blk P c).testBit r = P.testBit (512 * c + r) := by
  unfold CFSG.KC.Fi24Net.blk
  rw [nland, Nat.testBit_and, nshr, Nat.testBit_shiftRight, nmul, testBit_onesW, decide_eq_true hr,
    Bool.and_true, Nat.mul_comm c 512]

theorem kapLink_spec {OT : Nat → Nat} {K b : Nat} (h : kapLinkOK OT K b = true) {x : Nat}
    (hx : x < 306936) : K.testBit x = (OT (x / 512)).testBit (64 * (x % 512) + b) := by
  unfold kapLinkOK at h
  have hr : x % 512 < 512 := Nat.mod_lt _ (by decide)
  have hx' : 512 * (x / 512) + x % 512 = x := Nat.div_add_mod x 512
  have e := Nat.eq_of_beq_eq_true
    (allBelow_spec' h (x / 512) (by omega : x / 512 < 600) (by omega : x / 512 < 64 * 10))
  have e2 := congrArg (fun v => v.testBit (x % 512)) e
  simp only at e2
  rw [testBit_blk' K _ hr, hx', nland, Nat.testBit_and,
    testBit_rawPlane (rec := 64) (n := 512) (h := 9) (by decide) (by decide)] at e2
  rw [e2, decide_eq_true hr, Bool.true_and]
  by_cases h599 : x / 512 < 599
  · have hc : Nat.blt (x / 512) 599 = true := Nat.blt_eq.mpr h599
    rw [hc]
    change ((OT (x / 512)).testBit (64 * (x % 512) + b) && (ones 512).testBit (x % 512)) = _
    rw [testBit_onesW, decide_eq_true hr, Bool.and_true]
  · have hc : Nat.blt (x / 512) 599 = false :=
      Bool.eq_false_iff.mpr fun e => h599 (Nat.blt_eq.mp e)
    rw [hc]
    change ((OT (x / 512)).testBit (64 * (x % 512) + b) && (ones 248).testBit (x % 512)) = _
    rw [testBit_onesW, decide_eq_true (by omega : x % 512 < 248), Bool.and_true]

@[expose] def recF (OT : Nat → Nat) (b x : Nat) : Nat := ((OT (x / 512)) >>> (64 * (x % 512) + b)) % 2 ^ 19

theorem testBit_recF (OT : Nat → Nat) (b x : Nat) {k : Nat} (hk : k < 19) :
    (recF OT b x).testBit k = (OT (x / 512)).testBit (64 * (x % 512) + (b + k)) := by
  unfold recF
  rw [Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and, Nat.testBit_shiftRight, Nat.add_assoc]

theorem pF_rec {OT M : Nat → Nat} {b : Nat} (hv : NV M) (h : ∀ k < 19, genOK OT M b k = true) {x : Nat}
    (hx : x < 306936) : pF M x = recF OT b x := by
  have hx' : x < 524288 := by omega
  have hlt : recF OT b x < 524288 := Nat.mod_lt _ (by decide)
  refine eq_of_planes (pF_lt hv hx') hlt fun k hk => ?_
  rw [gen_spec hv hk (h k hk) hx', if_pos hx, testBit_recF OT b x hk]

theorem eE_rec {NW : Nat → Nat → Nat} {KA KB OT : Nat → Nat} {j b : Nat} (hn : netOK (NW j) = true)
    (hg : ∀ k < 19, genOK OT (NW j) b k = true) (ha : kapLinkOK OT (KA j) (b + 19) = true)
    (hb : kapLinkOK OT (KB j) (b + 20) = true) {N : Nat} (hN : N < 920808) :
    eE NW KA KB j N = 3 * recF OT b (N / 3) +
      (N % 3 + ((if (OT (N / 3 / 512)).testBit (64 * (N / 3 % 512) + (b + 19)) then 1 else 0) +
        (if (OT (N / 3 / 512)).testBit (64 * (N / 3 % 512) + (b + 20)) then 2 else 0))) % 3 := by
  have hp : N / 3 < 306936 := by omega
  rw [eE_eq hN, pF_rec (net_spec hn).1 hg hp]
  unfold kv
  rw [kapLink_spec ha hp, kapLink_spec hb hp]

end CFSG.KS.RouteP

end
