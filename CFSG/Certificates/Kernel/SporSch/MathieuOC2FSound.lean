module

public import Certificates.Data.Kernel.SporSch.MathieuOC2F
public import Mathlib.Logic.Function.Iterate
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11

theorem ptPow_succ (w m y e i : Nat) : ptPow w m y (e + 1) i = ptPow w m y e (pg w m y i) := rfl

theorem ptPow_eq (w m y : Nat) : ∀ e i, ptPow w m y e i = (pg w m y)^[e] i := by
  intro e
  induction e with
  | zero => intro i; rfl
  | succ e ih => intro i; rw [ptPow_succ, ih, Function.iterate_succ_apply]

theorem ordR_iter {n w m idn g : Nat} : ∀ k p, ordR n w m idn g k p = true →
    (pcomp n w m g)^[k] p = idn := by
  intro k
  induction k with
  | zero => intro p h; exact Nat.eq_of_beq_eq_true h
  | succ k ih =>
    intro p h
    have e : ordR n w m idn g (k + 1) p =
        bIf(Nat.beq p idn, false, strictB (pcomp n w m g p) (ordR n w m idn g k)) := rfl
    rw [e, CFSG.KS.PF.strictB_eqP] at h
    cases hb : Nat.beq p idn
    · rw [hb] at h
      rw [Function.iterate_succ_apply]
      exact ih _ h
    · rw [hb] at h
      exact absurd h Bool.false_ne_true

theorem pg_iter {n w g i : Nat} (hn : n < 2 ^ 32) (hi : i < n) : ∀ k p,
    pg w (mask w) ((pcomp n w (mask w) g)^[k] p) i = (pg w (mask w) g)^[k] (pg w (mask w) p i) := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    rw [Function.iterate_succ_apply, ih, CFSG.KS.PF.pg_pcomp hn hi, Function.iterate_succ_apply]

theorem fixPt_of_ordIs {n w idn y k i : Nat} (hn : n < 2 ^ 32) (hi : i < n)
    (h : ordIs n w (mask w) idn y k = true) : fixPt w (mask w) idn y (Nat.succ k) i = true := by
  have e := ordR_iter k y h
  have hp := pg_iter (w := w) (g := y) hn hi k y
  rw [e] at hp
  unfold fixPt
  rw [ptPow_eq, Function.iterate_succ_apply, ← hp]
  exact Nat.beq_refl _

theorem cntWord2F_eq {n w nw idn : Nat} {LR TR : Nat → Nat} {nb mx my : Nat}
    {ws : List (List Nat × Nat)} {R : Nat} (hn : n < 2 ^ 32) (h1 : 1 < n) :
    cntWord2F n w (mask w) nw idn LR TR nb mx my ws R = cntWord2K n w (mask w) nw idn LR TR nb mx my ws R := by
  funext k₀ k₁
  unfold cntWord2F cntWord2K
  refine congrArg (fun p => enumFrom n w (mask w) nw LR TR p (Nat.sub nb (nat_lit 2)) (nat_lit 2)
    (start2 n w (mask w) nw LR TR idn k₀ k₁) (nat_lit 0)) (funext fun y => ?_)
  cases ho : ordIs n w (mask w) idn y (Nat.sub my (nat_lit 1))
  · cases fixPt w (mask w) idn y (Nat.succ (Nat.sub my (nat_lit 1))) (nat_lit 0) <;>
      cases fixPt w (mask w) idn y (Nat.succ (Nat.sub my (nat_lit 1))) (nat_lit 1) <;> rfl
  · rw [fixPt_of_ordIs (i := nat_lit 0) hn (Nat.lt_trans Nat.zero_lt_one h1) ho,
      fixPt_of_ordIs (i := nat_lit 1) hn h1 ho]

end CFSG.KS.SporSch.MOC

end
