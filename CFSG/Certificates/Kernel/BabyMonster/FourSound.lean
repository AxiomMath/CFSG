module

public import CFSG.Certificates.Kernel.BabyMonster.F2Four
public import CFSG.Certificates.Kernel.BabyMonster.StripLib

public section

namespace CFSG.KC.BM.F4

open CFSG.KC.BM CFSG.KC.BM.SL

theorem forceBB_eq (v : Nat) (k : Nat → Bool) : forceBB v k = k v := by
  unfold forceBB
  cases Nat.beq v 0 <;> rfl

theorem mulW_cons (B : List Nat) (Ws : List (List Nat)) (A : Nat) :
    mulW (B :: Ws) A = mulW Ws (mulS B A) :=
  mulWn_cons 4370 B Ws A

@[expose] noncomputable def inner4 (t SMa SMb : Nat) (G : Nat → Nat → Nat → Nat → Bool)
    (Bs : List Nat) (E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
      Nat → Nat → Bool)
    (fun _ _ _ _ x0 y0 x1 y1 x2 y2 x3 y3 =>
      G (Nat.xor (Nat.shiftRight x0 t) (Nat.shiftRight y0 (Nat.succ t)))
        (Nat.xor (Nat.shiftRight x1 t) (Nat.shiftRight y1 (Nat.succ t)))
        (Nat.xor (Nat.shiftRight x2 t) (Nat.shiftRight y2 (Nat.succ t)))
        (Nat.xor (Nat.shiftRight x3 t) (Nat.shiftRight y3 (Nat.succ t))))
    (fun T _ ih2 E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3 =>
      (fun Ra Rb => ih2 (Nat.shiftRight E0 (nat_lit 4096)) (Nat.shiftRight E1 (nat_lit 4096))
          (Nat.shiftRight E2 (nat_lit 4096)) (Nat.shiftRight E3 (nat_lit 4096))
          (Nat.xor x0 (Nat.mul (Nat.land E0 LM) Ra))
          (Nat.xor y0 (Nat.mul (Nat.shiftRight
            (Nat.land E0 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
          (Nat.xor x1 (Nat.mul (Nat.land E1 LM) Ra))
          (Nat.xor y1 (Nat.mul (Nat.shiftRight
            (Nat.land E1 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
          (Nat.xor x2 (Nat.mul (Nat.land E2 LM) Ra))
          (Nat.xor y2 (Nat.mul (Nat.shiftRight
            (Nat.land E2 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb))
          (Nat.xor x3 (Nat.mul (Nat.land E3 LM) Ra))
          (Nat.xor y3 (Nat.mul (Nat.shiftRight
            (Nat.land E3 (nat_lit 340282366920938463463374607431768211455)) (nat_lit 64)) Rb)))
        (Nat.land T SMa) (Nat.land T SMb))
    Bs E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3

theorem inner4_eq (t SMa SMb : Nat) (G : Nat → Nat → Nat → Nat → Bool) :
    ∀ (Bs : List Nat) (E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3 : Nat),
    inner4 t SMa SMb G Bs E0 E1 E2 E3 x0 y0 x1 y1 x2 y2 x3 y3 =
      G (mInner t SMa SMb Bs E0 x0 y0) (mInner t SMa SMb Bs E1 x1 y1)
        (mInner t SMa SMb Bs E2 x2 y2) (mInner t SMa SMb Bs E3 x3 y3)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | T :: Bs, E0, E1, E2, E3, x0, y0, x1, y1, x2, y2, x3, y3 =>
    inner4_eq t SMa SMb G Bs (Nat.shiftRight E0 4096) (Nat.shiftRight E1 4096)
      (Nat.shiftRight E2 4096) (Nat.shiftRight E3 4096)
      (Nat.xor x0 (Nat.mul (Nat.land E0 LM) (Nat.land T SMa)))
      (Nat.xor y0 (Nat.mul (Nat.shiftRight
        (Nat.land E0 340282366920938463463374607431768211455) 64) (Nat.land T SMb)))
      (Nat.xor x1 (Nat.mul (Nat.land E1 LM) (Nat.land T SMa)))
      (Nat.xor y1 (Nat.mul (Nat.shiftRight
        (Nat.land E1 340282366920938463463374607431768211455) 64) (Nat.land T SMb)))
      (Nat.xor x2 (Nat.mul (Nat.land E2 LM) (Nat.land T SMa)))
      (Nat.xor y2 (Nat.mul (Nat.shiftRight
        (Nat.land E2 340282366920938463463374607431768211455) 64) (Nat.land T SMb)))
      (Nat.xor x3 (Nat.mul (Nat.land E3 LM) (Nat.land T SMa)))
      (Nat.xor y3 (Nat.mul (Nat.shiftRight
        (Nat.land E3 340282366920938463463374607431768211455) 64) (Nat.land T SMb)))

@[expose] noncomputable def round4 (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 u : Nat)
    (G : Nat → Nat → Nat → Nat → Bool) : Bool :=
  inner4 (Nat.add u u) (Nat.shiftLeft S (Nat.add u u)) (Nat.shiftLeft S (Nat.succ (Nat.add u u))) G
    Bs (Nat.shiftRight A0 (Nat.mul (nat_lit 64) (Nat.add u u)))
    (Nat.shiftRight A1 (Nat.mul (nat_lit 64) (Nat.add u u)))
    (Nat.shiftRight A2 (Nat.mul (nat_lit 64) (Nat.add u u)))
    (Nat.shiftRight A3 (Nat.mul (nat_lit 64) (Nat.add u u)))
    (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def fin4 (ih : Nat → Nat → Nat → Nat → Bool) (c0 c1 c2 c3 : Nat) :
    Nat → Nat → Nat → Nat → Bool :=
  fun r0 r1 r2 r3 => forceBB (Nat.xor c0 r0) (fun c0 => forceBB (Nat.xor c1 r1) (fun c1 =>
    forceBB (Nat.xor c2 r2) (fun c2 => forceBB (Nat.xor c3 r3) (fun c3 => ih c0 c1 c2 c3))))

@[expose] noncomputable def outer4 (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) (m : Nat) : Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun c0 c1 c2 c3 => k c0 c1 c2 c3)
    (fun u ih c0 c1 c2 c3 => round4 S Bs A0 A1 A2 A3 u (fin4 ih c0 c1 c2 c3)) m

theorem mulSG4_eq_outer4 (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) :
    mulSG4 S Bs A0 A1 A2 A3 k = outer4 S Bs A0 A1 A2 A3 k 32 0 0 0 0 := rfl

theorem outer4_succ (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) (m c0 c1 c2 c3 : Nat) :
    outer4 S Bs A0 A1 A2 A3 k (m + 1) c0 c1 c2 c3 =
      round4 S Bs A0 A1 A2 A3 m (fin4 (outer4 S Bs A0 A1 A2 A3 k m) c0 c1 c2 c3) := rfl

theorem round4_eq (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 u : Nat)
    (G : Nat → Nat → Nat → Nat → Bool) :
    round4 S Bs A0 A1 A2 A3 u G =
      G (mRound S Bs A0 u) (mRound S Bs A1 u) (mRound S Bs A2 u) (mRound S Bs A3 u) := by
  unfold round4
  rw [inner4_eq]
  rfl

theorem fin4_eq (ih : Nat → Nat → Nat → Nat → Bool) (c0 c1 c2 c3 r0 r1 r2 r3 : Nat) :
    fin4 ih c0 c1 c2 c3 r0 r1 r2 r3 = ih (Nat.xor c0 r0) (Nat.xor c1 r1) (Nat.xor c2 r2)
      (Nat.xor c3 r3) := by
  simp only [fin4, forceBB_eq]

theorem mOuter_succ (S : Nat) (Bs : List Nat) (A m acc : Nat) :
    mOuter S Bs A (m + 1) acc = mOuter S Bs A m (Nat.xor acc (mRound S Bs A m)) := rfl

theorem outer4_eq (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : ∀ (m c0 c1 c2 c3 : Nat),
    outer4 S Bs A0 A1 A2 A3 k m c0 c1 c2 c3 =
      k (mOuter S Bs A0 m c0) (mOuter S Bs A1 m c1) (mOuter S Bs A2 m c2) (mOuter S Bs A3 m c3)
  | 0, _, _, _, _ => rfl
  | m + 1, c0, c1, c2, c3 => by
    rw [outer4_succ, round4_eq, fin4_eq, outer4_eq S Bs A0 A1 A2 A3 k m, mOuter_succ, mOuter_succ,
      mOuter_succ, mOuter_succ]

theorem mulSG4_eq (S : Nat) (Bs : List Nat) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) :
    mulSG4 S Bs A0 A1 A2 A3 k =
      k (mOuter S Bs A0 32 0) (mOuter S Bs A1 32 0) (mOuter S Bs A2 32 0) (mOuter S Bs A3 32 0) := by
  rw [mulSG4_eq_outer4, outer4_eq]

theorem mulS4_eq (Bs : List Nat) (A0 A1 A2 A3 : Nat) (k : Nat → Nat → Nat → Nat → Bool) :
    mulS4 Bs A0 A1 A2 A3 k = k (mulS Bs A0) (mulS Bs A1) (mulS Bs A2) (mulS Bs A3) := by
  rw [mulS4, mulSG4_eq, mulS_eq, mulS_eq, mulS_eq, mulS_eq, mulSn_eq_mOuter, mulSn_eq_mOuter,
    mulSn_eq_mOuter, mulSn_eq_mOuter, SM_eq]

theorem mulW4_eq (k : Nat → Nat → Nat → Nat → Bool) : ∀ (Ws : List (List Nat)) (A0 A1 A2 A3 : Nat),
    mulW4 Ws A0 A1 A2 A3 k = k (mulW Ws A0) (mulW Ws A1) (mulW Ws A2) (mulW Ws A3)
  | [], _, _, _, _ => rfl
  | B :: Ws, A0, A1, A2, A3 => by
    change mulS4 B A0 A1 A2 A3 (fun a0 a1 a2 a3 => mulW4 Ws a0 a1 a2 a3 k) = _
    rw [mulS4_eq, mulW4_eq k Ws, mulW_cons, mulW_cons, mulW_cons, mulW_cons]

theorem beq4_spec {c0 c1 c2 c3 d0 d1 d2 d3 : Nat} (h : beq4 c0 c1 c2 c3 d0 d1 d2 d3 = true) :
    Nat.beq c0 d0 = true ∧ Nat.beq c1 d1 = true ∧ Nat.beq c2 d2 = true ∧ Nat.beq c3 d3 = true := by
  unfold beq4 at h
  simp only [andB_eq, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

theorem rhs4_eq (Ds : List (List Nat)) (C0 C1 C2 C3 c0 c1 c2 c3 : Nat) :
    rhs4 Ds C0 C1 C2 C3 c0 c1 c2 c3 =
      beq4 c0 c1 c2 c3 (mulW Ds C0) (mulW Ds C1) (mulW Ds C2) (mulW Ds C3) :=
  mulW4_eq _ Ds C0 C1 C2 C3

theorem mulW4_sound {Ws Ds : List (List Nat)} {A0 A1 A2 A3 C0 C1 C2 C3 : Nat}
    (h : mulW4 Ws A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW Ws A0) (mulW Ds C0) = true ∧ Nat.beq (mulW Ws A1) (mulW Ds C1) = true ∧
      Nat.beq (mulW Ws A2) (mulW Ds C2) = true ∧ Nat.beq (mulW Ws A3) (mulW Ds C3) = true := by
  rw [mulW4_eq, rhs4_eq] at h
  exact beq4_spec h

@[expose] noncomputable def sbFold (T : Nat) (blk : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun t => t)
    (fun R _ ih t => Bool.rec (motive := fun _ => Nat) (nat_lit 100000) (ih (Nat.succ t))
      (Nat.beq R (Nat.land (Nat.shiftRight T t) SM))) blk t

theorem sbFold_spec (T : Nat) : ∀ (blk : List Nat) (t : Nat), sbFold T blk t = 64 →
    blk.length + t = 64 ∧ ∀ i < blk.length, blk.getD i 0 = (T >>> (t + i)) &&& SM
  | [], t, h => by
    change t = 64 at h
    simp [h]
  | R :: blk, t, h => by
    change Bool.rec (motive := fun _ => Nat) 100000 (sbFold T blk (Nat.succ t))
      (Nat.beq R (Nat.land (Nat.shiftRight T t) SM)) = 64 at h
    cases hc : Nat.beq R (Nat.land (Nat.shiftRight T t) SM)
    · rw [hc] at h
      change (100000 : Nat) = 64 at h
      exact absurd h (by decide)
    · rw [hc] at h
      obtain ⟨h1, h2⟩ := sbFold_spec T blk (t + 1) h
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      intro i hi
      cases i with
      | zero => simpa using Nat.eq_of_beq_eq_true hc
      | succ i =>
        rw [List.getD_cons_succ, h2 i (by simp at hi; omega)]
        congr 2
        omega

theorem spreadBlkOK_spec {T : Nat} {blk : List Nat} (h : spreadBlkOK T blk = true) :
    blk.length = 64 ∧ ∀ t < 64, blk.getD t 0 = (T >>> t) &&& SM := by
  obtain ⟨h1, h2⟩ := sbFold_spec T blk 0 (Nat.eq_of_beq_eq_true h)
  refine ⟨by omega, fun t ht => ?_⟩
  rw [h2 t (by omega), Nat.zero_add]

theorem spreadOK_spec : ∀ {Rb : List (List Nat)} {Bs : List Nat}, spreadOK Rb Bs = true →
    Rb.length = Bs.length ∧ ∀ s < Rb.length,
      (Rb.getD s []).length = 64 ∧ ∀ t < 64, (Rb.getD s []).getD t 0 = (Bs.getD s 0 >>> t) &&& SM
  | [], [], _ => ⟨rfl, fun s hs => absurd hs (by simp)⟩
  | [], _ :: _, h => by
    change false = true at h
    exact absurd h (by decide)
  | _ :: _, [], h => by
    change false = true at h
    exact absurd h (by decide)
  | blk :: Rb, T :: Ts, h => by
    change andB (spreadBlkOK T blk) (spreadOK Rb Ts) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    obtain ⟨hl, hs⟩ := spreadOK_spec h.2
    refine ⟨by simp [hl], fun s hs' => ?_⟩
    cases s with
    | zero => simpa using spreadBlkOK_spec h.1
    | succ s =>
      rw [List.getD_cons_succ, List.getD_cons_succ]
      exact hs s (by simp at hs'; omega)

@[expose] noncomputable def rIn (blk : List Nat) (B acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun R _ ih2 B acc => ih2 (Nat.shiftRight B (nat_lit 64)) (Nat.xor acc (Nat.mul (Nat.land B LM) R)))
    blk B acc

@[expose] noncomputable def rOut (Rb : List (List Nat)) (E acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun blk _ ih E acc => ih (Nat.shiftRight E (nat_lit 4096)) (rIn blk (Nat.land E LMB) acc)) Rb E acc

@[expose] noncomputable def rIn4 (G : Nat → Nat → Nat → Nat → Bool) (blk : List Nat)
    (B0 B1 B2 B3 c0 c1 c2 c3 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ c0 c1 c2 c3 => G c0 c1 c2 c3)
    (fun R _ ih2 B0 B1 B2 B3 c0 c1 c2 c3 => ih2 (Nat.shiftRight B0 (nat_lit 64))
      (Nat.shiftRight B1 (nat_lit 64)) (Nat.shiftRight B2 (nat_lit 64))
      (Nat.shiftRight B3 (nat_lit 64))
      (Nat.xor c0 (Nat.mul (Nat.land B0 LM) R)) (Nat.xor c1 (Nat.mul (Nat.land B1 LM) R))
      (Nat.xor c2 (Nat.mul (Nat.land B2 LM) R)) (Nat.xor c3 (Nat.mul (Nat.land B3 LM) R)))
    blk B0 B1 B2 B3 c0 c1 c2 c3

theorem rIn4_eq (G : Nat → Nat → Nat → Nat → Bool) : ∀ (blk : List Nat) (B0 B1 B2 B3 c0 c1 c2 c3 : Nat),
    rIn4 G blk B0 B1 B2 B3 c0 c1 c2 c3 = G (rIn blk B0 c0) (rIn blk B1 c1) (rIn blk B2 c2) (rIn blk B3 c3)
  | [], _, _, _, _, _, _, _, _ => rfl
  | R :: blk, B0, B1, B2, B3, c0, c1, c2, c3 =>
    rIn4_eq G blk (Nat.shiftRight B0 64) (Nat.shiftRight B1 64) (Nat.shiftRight B2 64)
      (Nat.shiftRight B3 64) (Nat.xor c0 (Nat.mul (Nat.land B0 LM) R))
      (Nat.xor c1 (Nat.mul (Nat.land B1 LM) R)) (Nat.xor c2 (Nat.mul (Nat.land B2 LM) R))
      (Nat.xor c3 (Nat.mul (Nat.land B3 LM) R))

@[expose] noncomputable def fin4R (ih : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (E0 E1 E2 E3 : Nat) : Nat → Nat → Nat → Nat → Bool :=
  fun c0 c1 c2 c3 => forceBB c0 (fun c0 => forceBB c1 (fun c1 => forceBB c2 (fun c2 =>
    forceBB c3 (fun c3 => ih (Nat.shiftRight E0 (nat_lit 4096)) (Nat.shiftRight E1 (nat_lit 4096))
      (Nat.shiftRight E2 (nat_lit 4096)) (Nat.shiftRight E3 (nat_lit 4096)) c0 c1 c2 c3))))

@[expose] noncomputable def rOut4 (k : Nat → Nat → Nat → Nat → Bool) (Rb : List (List Nat)) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (fun _ _ _ _ c0 c1 c2 c3 => k c0 c1 c2 c3)
    (fun blk _ ih E0 E1 E2 E3 c0 c1 c2 c3 => rIn4 (fin4R ih E0 E1 E2 E3) blk (Nat.land E0 LMB)
      (Nat.land E1 LMB) (Nat.land E2 LMB) (Nat.land E3 LMB) c0 c1 c2 c3) Rb

theorem mulR4_eq_rOut4 (Rb : List (List Nat)) (A0 A1 A2 A3 : Nat)
    (k : Nat → Nat → Nat → Nat → Bool) : mulR4 Rb A0 A1 A2 A3 k = rOut4 k Rb A0 A1 A2 A3 0 0 0 0 :=
  rfl

theorem rOut4_cons (k : Nat → Nat → Nat → Nat → Bool) (blk : List Nat) (Rb : List (List Nat))
    (E0 E1 E2 E3 c0 c1 c2 c3 : Nat) :
    rOut4 k (blk :: Rb) E0 E1 E2 E3 c0 c1 c2 c3 = rIn4 (fin4R (rOut4 k Rb) E0 E1 E2 E3) blk
      (Nat.land E0 LMB) (Nat.land E1 LMB) (Nat.land E2 LMB) (Nat.land E3 LMB) c0 c1 c2 c3 := rfl

theorem rOut_cons (blk : List Nat) (Rb : List (List Nat)) (E acc : Nat) :
    rOut (blk :: Rb) E acc = rOut Rb (Nat.shiftRight E 4096) (rIn blk (Nat.land E LMB) acc) := rfl

theorem rOut4_eq (k : Nat → Nat → Nat → Nat → Bool) : ∀ (Rb : List (List Nat))
    (E0 E1 E2 E3 c0 c1 c2 c3 : Nat), rOut4 k Rb E0 E1 E2 E3 c0 c1 c2 c3 =
      k (rOut Rb E0 c0) (rOut Rb E1 c1) (rOut Rb E2 c2) (rOut Rb E3 c3)
  | [], _, _, _, _, _, _, _, _ => rfl
  | blk :: Rb, E0, E1, E2, E3, c0, c1, c2, c3 => by
    rw [rOut4_cons, rIn4_eq]
    simp only [fin4R, forceBB_eq]
    rw [rOut4_eq k Rb, rOut_cons, rOut_cons, rOut_cons, rOut_cons]

theorem rIn_bit (q : Nat) : ∀ (blk : List Nat) (B acc : Nat),
    bz ((rIn blk B acc).testBit q) = bz (acc.testBit q) +
      ∑ t ∈ Finset.range blk.length, bz ((((B >>> (64 * t)) &&& LM) * blk.getD t 0).testBit q)
  | [], B, acc => by
    change bz (acc.testBit q) = _
    simp
  | R :: blk, B, acc => by
    change bz ((rIn blk (Nat.shiftRight B 64) (Nat.xor acc (Nat.mul (Nat.land B LM) R))).testBit q) = _
    rw [rIn_bit q blk, List.length_cons, Finset.sum_range_succ']
    simp only [nxor, nshr, nland, nmul, Nat.testBit_xor, bz_xor, List.getD_cons_succ,
      List.getD_cons_zero, Nat.mul_zero, Nat.shiftRight_zero]
    have e : ∀ t, B >>> 64 >>> (64 * t) = B >>> (64 * (t + 1)) := by
      intro t
      rw [← Nat.shiftRight_add]
      congr 1
      ring
    simp only [e]
    ring

theorem rOut_bit (q : Nat) : ∀ (Rb : List (List Nat)) (E acc : Nat),
    bz ((rOut Rb E acc).testBit q) = bz (acc.testBit q) +
      ∑ s ∈ Finset.range Rb.length, ∑ t ∈ Finset.range (Rb.getD s []).length,
        bz (((((E >>> (4096 * s)) &&& LMB) >>> (64 * t) &&& LM) * (Rb.getD s []).getD t 0).testBit q)
  | [], E, acc => by
    change bz (acc.testBit q) = _
    simp
  | blk :: Rb, E, acc => by
    rw [rOut_cons, rOut_bit q Rb, rIn_bit, List.length_cons, Finset.sum_range_succ']
    simp only [nshr, nland, List.getD_cons_succ, List.getD_cons_zero, Nat.mul_zero,
      Nat.shiftRight_zero]
    have e : ∀ s, E >>> 4096 >>> (4096 * s) = E >>> (4096 * (s + 1)) := by
      intro s
      rw [← Nat.shiftRight_add]
      congr 1
      ring
    simp only [e]
    ring

theorem LMB_eq : LMB = 2 ^ 4096 - 1 := by
  unfold LMB
  rw [nsub, nshl, Nat.one_shiftLeft]

theorem spread_sparse (T t : Nat) : ∀ p, ((T >>> t) &&& SM).testBit p = true → p % 64 = 0 := by
  intro p hp
  rw [Nat.testBit_and, Bool.and_eq_true] at hp
  exact SMn_sparse 4370 p hp.2

theorem rOut_spread {Rb : List (List Nat)} {Bs : List Nat} (h : spreadOK Rb Bs = true) (A : Nat) :
    rOut Rb A 0 = mulS Bs A := by
  obtain ⟨hl, hb⟩ := spreadOK_spec h
  apply Nat.eq_of_testBit_eq
  intro q
  apply bz_inj
  have ht0 : q % 64 < 64 := Nat.mod_lt _ (by norm_num)
  rw [← Nat.div_add_mod q 64, rOut_bit, mulS_eq, mulSn_bit 4370 Bs A _ _ ht0, Nat.zero_testBit,
    bz_false, zero_add, ← hl, sum_range_mul64, Finset.sum_mul]
  generalize q / 64 = j
  generalize q % 64 = t0 at ht0
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨hlen, hrow⟩ := hb s (Finset.mem_range.1 hs)
  rw [hlen, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have ht := Finset.mem_range.1 ht
  rw [hrow t ht, testBit_mul_sparse (col_lt _) j _ (spread_sparse _ _) t0 ht0, testBit_col _ _ ht0,
    Nat.testBit_shiftRight, Nat.testBit_and, LMB_eq, Nat.testBit_two_pow_sub_one,
    decide_eq_true (by omega : 64 * t + t0 < 4096), Bool.and_true, Nat.testBit_shiftRight,
    Nat.testBit_and, Nat.testBit_shiftRight, SM_eq, testBit_SMn_mul]
  have e1 : (64 * s + t) / 64 = s := by omega
  have e2 : (64 * s + t) % 64 = t := by omega
  have e3 : 4096 * s + (64 * t + t0) = 64 * (64 * s + t) + t0 := by ring
  have e4 : t + 64 * j = 64 * j + t := by ring
  rw [e1, e2, e3, e4, bz_and, bz_and]
  ring

theorem mulR4_eq {Rb : List (List Nat)} {Bs : List Nat} (h : spreadOK Rb Bs = true)
    (A0 A1 A2 A3 : Nat) (k : Nat → Nat → Nat → Nat → Bool) :
    mulR4 Rb A0 A1 A2 A3 k = k (mulS Bs A0) (mulS Bs A1) (mulS Bs A2) (mulS Bs A3) := by
  rw [mulR4_eq_rOut4, rOut4_eq, rOut_spread h, rOut_spread h, rOut_spread h, rOut_spread h]

theorem mulR4_sound {Rb : List (List Nat)} {Bs : List Nat} {Ds : List (List Nat)}
    {A0 A1 A2 A3 C0 C1 C2 C3 : Nat} (hR : spreadOK Rb Bs = true)
    (h : mulR4 Rb A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW [Bs] A0) (mulW Ds C0) = true ∧ Nat.beq (mulW [Bs] A1) (mulW Ds C1) = true ∧
      Nat.beq (mulW [Bs] A2) (mulW Ds C2) = true ∧ Nat.beq (mulW [Bs] A3) (mulW Ds C3) = true := by
  rw [mulR4_eq hR, rhs4_eq] at h
  simp only [mulW_cons]
  exact beq4_spec h

theorem mulW4_sound0 (Ws Ds : List (List Nat)) (A0 A1 A2 A3 C0 C1 C2 C3 : Nat)
    (h : mulW4 Ws A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW Ws A0) (mulW Ds C0) = true := (mulW4_sound h).1

theorem mulW4_sound1 (Ws Ds : List (List Nat)) (A0 A1 A2 A3 C0 C1 C2 C3 : Nat)
    (h : mulW4 Ws A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW Ws A1) (mulW Ds C1) = true := (mulW4_sound h).2.1

theorem mulW4_sound2 (Ws Ds : List (List Nat)) (A0 A1 A2 A3 C0 C1 C2 C3 : Nat)
    (h : mulW4 Ws A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW Ws A2) (mulW Ds C2) = true := (mulW4_sound h).2.2.1

theorem mulW4_sound3 (Ws Ds : List (List Nat)) (A0 A1 A2 A3 C0 C1 C2 C3 : Nat)
    (h : mulW4 Ws A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW Ws A3) (mulW Ds C3) = true := (mulW4_sound h).2.2.2

theorem mulR4_sound0 (Rb : List (List Nat)) (Bs : List Nat) (Ds : List (List Nat))
    (A0 A1 A2 A3 C0 C1 C2 C3 : Nat) (hR : spreadOK Rb Bs = true)
    (h : mulR4 Rb A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW [Bs] A0) (mulW Ds C0) = true := (mulR4_sound hR h).1

theorem mulR4_sound1 (Rb : List (List Nat)) (Bs : List Nat) (Ds : List (List Nat))
    (A0 A1 A2 A3 C0 C1 C2 C3 : Nat) (hR : spreadOK Rb Bs = true)
    (h : mulR4 Rb A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW [Bs] A1) (mulW Ds C1) = true := (mulR4_sound hR h).2.1

theorem mulR4_sound2 (Rb : List (List Nat)) (Bs : List Nat) (Ds : List (List Nat))
    (A0 A1 A2 A3 C0 C1 C2 C3 : Nat) (hR : spreadOK Rb Bs = true)
    (h : mulR4 Rb A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW [Bs] A2) (mulW Ds C2) = true := (mulR4_sound hR h).2.2.1

theorem mulR4_sound3 (Rb : List (List Nat)) (Bs : List Nat) (Ds : List (List Nat))
    (A0 A1 A2 A3 C0 C1 C2 C3 : Nat) (hR : spreadOK Rb Bs = true)
    (h : mulR4 Rb A0 A1 A2 A3 (rhs4 Ds C0 C1 C2 C3) = true) :
    Nat.beq (mulW [Bs] A3) (mulW Ds C3) = true := (mulR4_sound hR h).2.2.2

end CFSG.KC.BM.F4

end
