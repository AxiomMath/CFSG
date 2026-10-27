module

public import CFSG.Certificates.Kernel.Common.Loop
public meta import Lean
public import Lean.Exception

public section

namespace CFSG.KC.Cover

@[expose] noncomputable def blockK (n lo B : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun d acc => bAnd(bIf(Nat.blt (Nat.add lo d) n, f (Nat.add lo d), true), acc)) B

theorem blockK_spec {n lo B : Nat} {f : Nat → Bool} (h : blockK n lo B f = true) :
    ∀ d < B, lo + d < n → f (lo + d) = true := by
  induction B with
  | zero => intro d hd; omega
  | succ B ih =>
    intro d hd hn
    have e : blockK n lo (B + 1) f =
        (Bool.rec (motive := fun _ => Bool) false (blockK n lo B f)
          (Bool.rec (motive := fun _ => Bool) true (f (lo + B)) (Nat.blt (lo + B) n))) :=
      rfl
    rw [e] at h
    cases hc : Bool.rec (motive := fun _ => Bool) true (f (lo + B)) (Nat.blt (lo + B) n)
    · rw [hc] at h
      exact absurd h Bool.false_ne_true
    · rw [hc] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | hd
      · exact ih h d hd hn
      · subst hd
        have hb : Nat.blt (lo + d) n = true := Nat.ble_eq_true_of_le hn
        rw [hb] at hc
        exact hc

theorem cover_zero (n B : Nat) (f : Nat → Bool) : ∀ t, t < Nat.mul B 0 → t < n → f t = true := by
  intro t ht
  rw [Nat.mul_eq, Nat.mul_zero] at ht
  omega

theorem cover_succ (n B m : Nat) (f : Nat → Bool) (hb : blockK n (Nat.mul B m) B f = true)
    (ih : ∀ t, t < Nat.mul B m → t < n → f t = true) :
    ∀ t, t < Nat.mul B (Nat.succ m) → t < n → f t = true := by
  intro t ht hn
  rw [Nat.mul_eq] at ih hb ht
  by_cases h : t < B * m
  · exact ih t h hn
  · have hd := blockK_spec hb (t - B * m) (by rw [Nat.mul_succ] at ht; omega) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at hd

theorem cover_done (n B nb : Nat) (f : Nat → Bool) (hn : Nat.ble n (Nat.mul B nb) = true)
    (h : ∀ t, t < Nat.mul B nb → t < n → f t = true) : ∀ t, t < n → f t = true := by
  intro t ht
  have := Nat.le_of_ble_eq_true hn
  exact h t (by omega) ht

end CFSG.KC.Cover

end

open Lean Meta Elab Tactic in
elab "kc_cover " bN:num : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let .forallE tn tt (.forallE _ hlt body _) _ := ty
    | throwError "kc_cover: the goal is not `∀ t < n, F t = true`"
  unless hlt.isAppOfArity ``LT.lt 4 do throwError "kc_cover: the bound is not `t < n`"
  let some n := hlt.appArg!.rawNatLit? <|> hlt.appArg!.nat?
    | throwError "kc_cover: the bound is not a numeral"
  let some (_, lhs, _) := (body.lowerLooseBVars 1 1).eq?
    | throwError "kc_cover: the body is not `F t = true`"
  let B := bN.getNat
  unless 0 < B ∧ 0 < n do throwError "kc_cover: empty block or range"
  let f := Expr.lam tn tt lhs .default
  let nb := (n + B - 1) / B
  let lit := mkRawNatLit
  let mut pf := mkAppN (mkConst ``CFSG.KC.Cover.cover_zero) #[lit n, lit B, f]
  for k in [0:nb] do
    let bty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KC.Cover.blockK)
        #[lit n, mkApp2 (mkConst ``Nat.mul) (lit B) (lit k), lit B, f])
      (mkConst ``Bool.true)
    let blk ← mkAuxLemma [] bty reflBoolTrue (kind? := `blk) (cache := false)
    pf := mkAppN (mkConst ``CFSG.KC.Cover.cover_succ) #[lit n, lit B, lit k, f, mkConst blk, pf]
  g.assign (mkAppN (mkConst ``CFSG.KC.Cover.cover_done) #[lit n, lit B, lit nb, f, reflBoolTrue, pf])
