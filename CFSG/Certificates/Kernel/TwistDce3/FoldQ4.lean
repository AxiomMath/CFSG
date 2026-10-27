module

public import Certificates.Data.Kernel.TwistDce3.FoldQ4
public import CFSG.Certificates.Kernel.TwistDce3.FoldQ
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.TwDce3.FoldQ

open CFSG.KC.TwDce (sB wLen wStr fld)
open CFSG.KC.YModel (fieldAt)
open CFSG.KC.TwDce3 (isOne evP)
open CFSG.KC.TwDce3Q (ev4Q ev4T isOneQ4)
open CFSG.Certificates.TwDce.Words (sB_eq)
open CFSG.Certificates.TwDce3.Words (land15 shr4)

section
variable (PB : ℕ) (F : ℕ → ℕ)

theorem ev4T_succ (k : ℕ → ℕ → ℕ → ℕ → Bool) (n s x y z v : ℕ) :
    ev4T PB F (n + 1) s x y z v k = ev4T PB F n (Nat.shiftRight s 4)
      (fieldAt PB (F (Nat.land s 15)) x) (fieldAt PB (F (Nat.land s 15)) y)
      (fieldAt PB (F (Nat.land s 15)) z) (fieldAt PB (F (Nat.land s 15)) v) k := by
  unfold ev4T
  simp only [Nat.rec_add_one, sB_eq]

theorem ev4T_eq (k : ℕ → ℕ → ℕ → ℕ → Bool) : ∀ n s x y z v,
    ev4T PB F n s x y z v k = k (mv PB F (dg n s) x) (mv PB F (dg n s) y) (mv PB F (dg n s) z)
      (mv PB F (dg n s) v) := by
  intro n
  induction n with
  | zero => intro s x y z v; rfl
  | succ n ih =>
    intro s x y z v
    rw [ev4T_succ, ih, land15, shr4, dg_succ, mv_cons, mv_cons, mv_cons, mv_cons]

theorem ev4Q_succ (k : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (q s x y z v : ℕ) :
    ev4Q PB F (q + 1) s x y z v k = ev4Q PB F q (Nat.shiftRight s 16)
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) x))))
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) y))))
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) z))))
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) v)))) k := by
  unfold ev4Q
  simp only [Nat.rec_add_one, sB_eq]

theorem ev4Q_eq (k : ℕ → ℕ → ℕ → ℕ → ℕ → Bool) : ∀ q s x y z v,
    ev4Q PB F q s x y z v k = k (s / 16 ^ (4 * q)) (mv PB F (dg (4 * q) s) x)
      (mv PB F (dg (4 * q) s) y) (mv PB F (dg (4 * q) s) z) (mv PB F (dg (4 * q) s) v) := by
  intro q
  induction q with
  | zero => intro s x y z v; simp only [Nat.mul_zero, pow_zero, Nat.div_one]; rfl
  | succ q ih =>
    intro s x y z v
    rw [ev4Q_succ, ih, land15, land15, land15, land15, shr4, shr8, shr12, shr16, div16_four,
      show 4 * (q + 1) = 4 * q + 4 by ring, dg_four]
    simp only [mv_cons]

theorem andB4 (a b c d : Bool) : CFSG.KC.andB a (CFSG.KC.andB b (CFSG.KC.andB c d)) =
    CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB true a) b) c) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem isOne4_eq (BS w : ℕ) : isOne PB F BS 4 w =
    CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB true
      (sB (fld BS (Nat.mul 16 0) 65535) fun b => Nat.beq (evP PB F w b) b))
      (sB (fld BS (Nat.mul 16 1) 65535) fun b => Nat.beq (evP PB F w b) b))
      (sB (fld BS (Nat.mul 16 2) 65535) fun b => Nat.beq (evP PB F w b) b))
      (sB (fld BS (Nat.mul 16 3) 65535) fun b => Nat.beq (evP PB F w b) b) := by
  unfold isOne
  rw [sB_eq]
  rfl

theorem isOneQ4_eq (BS w : ℕ) : isOneQ4 PB F BS w = isOne PB F BS 4 w := by
  rw [isOne4_eq]
  unfold isOneQ4
  simp only [sB_eq]
  rw [ev4Q_eq, ev4T_eq, shr2, land3, ← mv_split, ← mv_split, ← mv_split, ← mv_split, evP_mv,
    evP_mv, evP_mv, evP_mv]
  exact andB4 _ _ _ _

end

section
variable (PB : ℕ) (F : ℕ → ℕ) (INVM BS NB NT PSF PSB : ℕ) (RD RW RA WD RJ : ℕ → ℕ)

theorem foldRange_isOneQ4 (a n S : ℕ) :
    CFSG.KC.TwDce3Q.foldRange (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ a n S =
      CFSG.KC.TwDce3.foldRange PB F INVM BS 4 NT PSF PSB RD RW RA WD RJ a n S := by
  rw [show isOneQ4 PB F BS = isOne PB F BS 4 from funext (isOneQ4_eq PB F BS)]
  exact foldRange_isOne PB F INVM BS 4 NT PSF PSB RD RW RA WD RJ a n S

theorem fold_of4 {a n S S' : ℕ} (hNB : NB = 4)
    (h : CFSG.KC.TwDce3Q.foldIs (isOneQ4 PB F BS) INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    CFSG.KC.TwDce3.foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' := by
  subst hNB
  rw [← foldRange_isOneQ4]
  exact Nat.eq_of_beq_eq_true h

end

end CFSG.Certificates.TwDce3.FoldQ

end
