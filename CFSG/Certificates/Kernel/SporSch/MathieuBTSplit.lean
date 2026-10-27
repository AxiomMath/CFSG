module

public import Certificates.Data.Kernel.SporSch.MathieuBTSplit
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KS.SporSch.MBT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC Finset

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem foldBlk_add' {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (b : Nat) : ∀ len s, foldBlk b f len s = s + ∑ l ∈ range len, g (b + l)
  | 0, s => by simp [foldBlk]
  | len + 1, s => by
    change strictN (f (Nat.add b len) s) (foldBlk b f len) = _
    rw [strictN_eq', foldBlk_add' hf b len, hf, sum_range_succ]
    simp only [Nat.add_eq]
    omega

theorem foldN_add' {f : Nat → Nat → Nat} {g : Nat → Nat} (hf : ∀ i s, f i s = s + g i)
    (n s : Nat) : foldN n f s = s + ∑ i ∈ range n, g i := by
  have sl : ∀ a, Nat.shiftLeft a (nat_lit 6) = 64 * a := fun a => by
    rw [Nat.mul_comm]
    exact Nat.shiftLeft_eq a 6
  have key : ∀ q s', Nat.rec (motive := fun _ => Nat → Nat) (fun s => s)
      (fun h ih s => strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s) ih) q s' =
      s' + ∑ i ∈ range (64 * q), g i := by
    intro q
    induction q with
    | zero => intro s'; simp
    | succ h ih =>
      intro s'
      change strictN (foldBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) s') _ = _
      rw [strictN_eq', ih, foldBlk_add' hf, Nat.mul_succ, sum_range_add, sl]
      ring
  have e1 : Nat.land n (nat_lit 63) = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6
  have e2 : Nat.shiftRight n (nat_lit 6) = n / 64 := Nat.shiftRight_eq_div_pow n 6
  unfold foldN
  dsimp only
  rw [key, foldBlk_add' hf, e1, e2, sl]
  conv_rhs => rw [← Nat.div_add_mod n 64, sum_range_add]
  ring

theorem foldUp_acc {F : Nat → Nat → Nat} (hF : ∀ t s, F t s = s + F t 0) (n s : Nat) :
    foldUp n F s = s + ∑ t ∈ range n, F t 0 := by
  unfold foldUp
  rw [foldN_add' (g := fun i => F (Nat.sub (Nat.sub n 1) i) 0) (fun i s => hF _ s)]
  congr 1
  exact sum_range_reflect (fun t => F t 0) n

variable {n w m nw BP : Nat} {LR TR TRI : Nat → Nat} {X Y : Nat}

theorem btGo_succ (d i h hi s : Nat) : btGo n w m nw BP LR TR TRI X Y (d + 1) i h hi s =
    strictN (LR i) (fun R => strictN (pg w m BP i) (fun b =>
      strictN (roff n nw R) (fun o => strictN (fwdK n w m BP X i) (fun fc =>
      nIf(Nat.beq fc (nat_lit 0),
        strictN (walkK w m X b n b (nat_lit 0)) (fun lb =>
          foldUp (rcnt R) (fun t s => strictN (pg w m h (rpt w m R t)) (fun q =>
            nIf(Nat.beq (walkK w m Y q n q (nat_lit 0)) lb,
              btGo n w m nw BP LR TR TRI X Y d (Nat.succ i) (pcomp n w m h (TR (Nat.add o t)))
                (pcomp n w m (TRI (Nat.add o t)) hi) s, s))) s),
        strictN (Nat.pred fc) (fun c =>
          strictN (rpos w m nw R (pg w m hi (itF (fun p => pg w m Y p) (Nat.div c (nat_lit 64))
            (pg w m h (pg w m BP (Nat.mod c (nat_lit 64))))))) (fun t =>
          nIf(Nat.blt t (rcnt R),
            btGo n w m nw BP LR TR TRI X Y d (Nat.succ i) (pcomp n w m h (TR (Nat.add o t)))
              (pcomp n w m (TRI (Nat.add o t)) hi) s, s)))))))) := rfl

theorem btGo_acc : ∀ d i h hi s, btGo n w m nw BP LR TR TRI X Y d i h hi s =
    s + btGo n w m nw BP LR TR TRI X Y d i h hi 0
  | 0, i, h, hi, s => by
    change Bool.rec (motive := fun _ => Nat) s (Nat.succ s) _ =
      s + Bool.rec (motive := fun _ => Nat) 0 (Nat.succ 0) _
    cases Nat.beq (pcomp n w m h X) (pcomp n w m Y h) <;> rfl
  | d + 1, i, h, hi, s => by
    rw [btGo_succ, btGo_succ]
    simp only [strictN_eq']
    cases Nat.beq (fwdK n w m BP X i) 0
    · dsimp only
      cases Nat.blt _ _
      · rfl
      · exact btGo_acc d _ _ _ s
    · dsimp only
      rw [foldUp_acc, foldUp_acc (s := 0), Nat.zero_add]
      all_goals intro t s'
      all_goals cases Nat.beq _ _
      all_goals first | rfl | exact btGo_acc d _ _ _ s' 

theorem btR_eq (k lo len : Nat) : btR n w m nw BP LR TR TRI X Y k lo len =
    ∑ l ∈ range len, btBr n w m nw BP LR TR TRI X Y k (lo + l) := by
  unfold btR
  exact (foldBlk_add' (f := fun t s => Nat.add s (btBr n w m nw BP LR TR TRI X Y k t))
    (g := btBr n w m nw BP LR TR TRI X Y k) (fun _ _ => rfl) lo len 0).trans (Nat.zero_add _)

theorem btR_add (k lo a b : Nat) : btR n w m nw BP LR TR TRI X Y k lo (a + b) =
    btR n w m nw BP LR TR TRI X Y k lo a + btR n w m nw BP LR TR TRI X Y k (lo + a) b := by
  simp only [btR_eq, sum_range_add, Nat.add_assoc]

theorem btR_join {k lo a b N v u C lo' : Nat}
    (h1 : Nat.beq (btR n w m nw BP LR TR TRI X Y k lo a) v = true) (hl : lo + a = lo')
    (h2 : btR n w m nw BP LR TR TRI X Y k lo' b = u) (hN : a + b = N) (hC : v + u = C) :
    btR n w m nw BP LR TR TRI X Y k lo N = C := by
  rw [← hN, btR_add, Nat.eq_of_beq_eq_true h1, hl, h2, hC]

theorem btK_eq_btR (k : Nat) : btK n w m nw BP (k + 1) LR TR TRI X Y =
    btR n w m nw BP LR TR TRI X Y k 0 (rcnt (LR 0)) := by
  unfold btK
  rw [btGo_succ]
  have h0 : fwdK n w m BP X 0 = 0 := rfl
  simp only [strictN_eq', h0]
  change foldUp _ _ 0 = _
  rw [foldUp_acc, Nat.zero_add, btR_eq]
  · refine sum_congr rfl fun t _ => ?_
    unfold btBr
    simp only [strictN_eq', Nat.zero_add]
  · intro t s'
    cases Nat.beq _ _
    · rfl
    · exact btGo_acc k _ _ _ s'

theorem btK_of_btR {k N C : Nat} (hN : Nat.beq (rcnt (LR 0)) N = true)
    (h : btR n w m nw BP LR TR TRI X Y k 0 N = C) : btK n w m nw BP (k + 1) LR TR TRI X Y = C := by
  rw [btK_eq_btR, Nat.eq_of_beq_eq_true hN, h]

end CFSG.KS.SporSch.MBT

end
