module

public import Certificates.Data.Kernel.TwistDce3.FoldQ
public import CFSG.Certificates.Kernel.TwistDce3.Words
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.TwDce3.FoldQ

open CFSG.KC.TwDce (sB wLen wStr fld)
open CFSG.KC.YModel (fieldAt)
open CFSG.KC.TwDce3 (isOne evP)
open CFSG.KC.TwDce3Q (ev3Q ev3T isOneQ)
open CFSG.Certificates.TwDce.Words (sB_eq lst)
open CFSG.Certificates.TwDce3.Words (land15 shr4 digs_succ evP_eq lst_eq)

@[expose] noncomputable def dg (n s : ℕ) : List ℕ := (List.range n).map (fun i => s / 16 ^ i % 16)

@[expose] noncomputable def mv (PB : ℕ) (F : ℕ → ℕ) (l : List ℕ) (x : ℕ) : ℕ :=
  l.foldl (fun p c => fieldAt PB (F c) p) x

theorem dg_succ (n s : ℕ) : dg (n + 1) s = s % 16 :: dg n (s / 16) := digs_succ s n

theorem dg_add (m r s : ℕ) : dg (m + r) s = dg m s ++ dg r (s / 16 ^ m) := by
  unfold dg
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  change s / 16 ^ (m + i) % 16 = s / 16 ^ m / 16 ^ i % 16
  rw [pow_add, Nat.div_div_eq_div_mul]

theorem mv_cons (PB : ℕ) (F : ℕ → ℕ) (c : ℕ) (l : List ℕ) (x : ℕ) :
    mv PB F (c :: l) x = mv PB F l (fieldAt PB (F c) x) := rfl

theorem mv_append (PB : ℕ) (F : ℕ → ℕ) (l l' : List ℕ) (x : ℕ) :
    mv PB F (l ++ l') x = mv PB F l' (mv PB F l x) := List.foldl_append

theorem shr8 (s : ℕ) : Nat.shiftRight s 8 = s / 16 / 16 := by
  rw [show Nat.shiftRight s 8 = s >>> 8 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul]

theorem shr12 (s : ℕ) : Nat.shiftRight s 12 = s / 16 / 16 / 16 := by
  rw [show Nat.shiftRight s 12 = s >>> 12 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

theorem shr16 (s : ℕ) : Nat.shiftRight s 16 = s / 16 / 16 / 16 / 16 := by
  rw [show Nat.shiftRight s 16 = s >>> 16 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]

section
variable (PB : ℕ) (F : ℕ → ℕ)

theorem ev3T_succ (k : ℕ → ℕ → ℕ → Bool) (n s x y z : ℕ) :
    ev3T PB F (n + 1) s x y z k = ev3T PB F n (Nat.shiftRight s 4)
      (fieldAt PB (F (Nat.land s 15)) x) (fieldAt PB (F (Nat.land s 15)) y)
      (fieldAt PB (F (Nat.land s 15)) z) k := by
  unfold ev3T
  simp only [Nat.rec_add_one, sB_eq]

theorem ev3T_eq (k : ℕ → ℕ → ℕ → Bool) : ∀ n s x y z,
    ev3T PB F n s x y z k = k (mv PB F (dg n s) x) (mv PB F (dg n s) y) (mv PB F (dg n s) z) := by
  intro n
  induction n with
  | zero => intro s x y z; rfl
  | succ n ih =>
    intro s x y z
    rw [ev3T_succ, ih, land15, shr4, dg_succ, mv_cons, mv_cons, mv_cons]

theorem ev3Q_succ (k : ℕ → ℕ → ℕ → ℕ → Bool) (q s x y z : ℕ) :
    ev3Q PB F (q + 1) s x y z k = ev3Q PB F q (Nat.shiftRight s 16)
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) x))))
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) y))))
      (fieldAt PB (F (Nat.land (Nat.shiftRight s 12) 15)) (fieldAt PB (F (Nat.land (Nat.shiftRight s 8) 15))
        (fieldAt PB (F (Nat.land (Nat.shiftRight s 4) 15)) (fieldAt PB (F (Nat.land s 15)) z)))) k := by
  unfold ev3Q
  simp only [Nat.rec_add_one, sB_eq]

theorem dg_four (n s : ℕ) : dg (n + 4) s =
    s % 16 :: s / 16 % 16 :: s / 16 / 16 % 16 :: s / 16 / 16 / 16 % 16 ::
      dg n (s / 16 / 16 / 16 / 16) := by
  rw [show n + 4 = n + 3 + 1 by omega, dg_succ, show n + 3 = n + 2 + 1 by omega, dg_succ,
    show n + 2 = n + 1 + 1 by omega, dg_succ, dg_succ]

theorem div16_four (s q : ℕ) : s / 16 / 16 / 16 / 16 / 16 ^ (4 * q) = s / 16 ^ (4 * (q + 1)) := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
    Nat.div_div_eq_div_mul]
  congr 1
  ring

theorem ev3Q_eq (k : ℕ → ℕ → ℕ → ℕ → Bool) : ∀ q s x y z,
    ev3Q PB F q s x y z k = k (s / 16 ^ (4 * q)) (mv PB F (dg (4 * q) s) x)
      (mv PB F (dg (4 * q) s) y) (mv PB F (dg (4 * q) s) z) := by
  intro q
  induction q with
  | zero => intro s x y z; simp only [Nat.mul_zero, pow_zero, Nat.div_one]; rfl
  | succ q ih =>
    intro s x y z
    rw [ev3Q_succ, ih, land15, land15, land15, land15, shr4, shr8, shr12, shr16, div16_four,
      show 4 * (q + 1) = 4 * q + 4 by ring, dg_four]
    simp only [mv_cons]

theorem shr2 (n : ℕ) : Nat.shiftRight n 2 = n / 4 := by
  rw [show Nat.shiftRight n 2 = n >>> 2 from rfl, Nat.shiftRight_eq_div_pow]

theorem land3 (n : ℕ) : Nat.land n 3 = n % 4 := by
  change n &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem mv_split (n s x : ℕ) :
    mv PB F (dg n s) x = mv PB F (dg (n % 4) (s / 16 ^ (4 * (n / 4)))) (mv PB F (dg (4 * (n / 4)) s) x) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  rw [dg_add, mv_append]

theorem evP_mv (w x : ℕ) : evP PB F w x = mv PB F (dg (wLen w) (wStr w)) x := by
  rw [evP_eq, lst_eq]
  rfl

theorem andB3 (a b c : Bool) : CFSG.KC.andB a (CFSG.KC.andB b c) =
    CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB true a) b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem isOne3_eq (BS w : ℕ) : isOne PB F BS 3 w =
    CFSG.KC.andB (CFSG.KC.andB (CFSG.KC.andB true
      (sB (fld BS (Nat.mul 16 0) 65535) fun b => Nat.beq (evP PB F w b) b))
      (sB (fld BS (Nat.mul 16 1) 65535) fun b => Nat.beq (evP PB F w b) b))
      (sB (fld BS (Nat.mul 16 2) 65535) fun b => Nat.beq (evP PB F w b) b) := by
  unfold isOne
  rw [sB_eq]
  rfl

theorem isOneQ_eq (BS w : ℕ) : isOneQ PB F BS w = isOne PB F BS 3 w := by
  rw [isOne3_eq]
  unfold isOneQ
  simp only [sB_eq]
  rw [ev3Q_eq, ev3T_eq, shr2, land3, ← mv_split, ← mv_split, ← mv_split, evP_mv, evP_mv, evP_mv]
  exact andB3 _ _ _

end

section
variable (iO : ℕ → Bool) (PB : ℕ) (F : ℕ → ℕ) (INVM BS NB NT PSF PSB : ℕ) (RD RW RA WD RJ : ℕ → ℕ)

theorem foldRange_isOne (a n S : ℕ) :
    CFSG.KC.TwDce3Q.foldRange (isOne PB F BS NB) INVM NT PSF PSB RD RW RA WD RJ a n S =
      CFSG.KC.TwDce3.foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S := rfl

theorem foldRange_isOneQ (a n S : ℕ) :
    CFSG.KC.TwDce3Q.foldRange (isOneQ PB F BS) INVM NT PSF PSB RD RW RA WD RJ a n S =
      CFSG.KC.TwDce3.foldRange PB F INVM BS 3 NT PSF PSB RD RW RA WD RJ a n S := by
  rw [show isOneQ PB F BS = isOne PB F BS 3 from funext (isOneQ_eq PB F BS)]
  exact foldRange_isOne PB F INVM BS 3 NT PSF PSB RD RW RA WD RJ a n S

theorem fold_of {a n S S' : ℕ} (hNB : NB = 3)
    (h : CFSG.KC.TwDce3Q.foldIs (isOneQ PB F BS) INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    CFSG.KC.TwDce3.foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' := by
  subst hNB
  rw [← foldRange_isOneQ]
  exact Nat.eq_of_beq_eq_true h

end

end CFSG.Certificates.TwDce3.FoldQ

end
