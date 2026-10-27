module

public import CFSG.Certificates.Kernel.LyOmega.Defs
public import Certificates.Data.Kernel.LyOmega.Base
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section
namespace CFSG.KS.LyOm.SB4
open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KS.LyOm CFSG.KC.Loop

private theorem nIf_eq' (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by
  cases c <;> rfl

private theorem bAnd_eq' (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

private theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

private theorem bEnt_eq (X i j : ℕ) : bEnt X i j = X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 := by
  unfold bEnt fldW
  change (X >>> (1332 * i + 12 * j)) &&& (2 ^ 12 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem run_spec (X : ℕ) (cs : List Char) : ∀ i, digLanesRun X cs i ≠ 1048576 →
    digLanesRun X cs i = i + (cs.filter (· ≠ '\n')).length ∧
      ∀ k (hk : k < (cs.filter (· ≠ '\n')).length),
        48 ≤ ((cs.filter (· ≠ '\n'))[k]).toNat ∧
        ((cs.filter (· ≠ '\n'))[k]).toNat - 48 = bEnt X ((i + k) / 111) ((i + k) % 111) := by
  induction cs with
  | nil => intro i _; exact ⟨rfl, fun k hk => absurd hk (by simp)⟩
  | cons ch cs ih =>
    intro i hi
    have e : digLanesRun X (ch :: cs) i = strictN (Char.toNat ch) (fun c =>
        nIf(Nat.beq c (nat_lit 10), digLanesRun X cs i,
          nIf(bAnd(Nat.ble (nat_lit 48) c, bAnd(Nat.ble c (nat_lit 57),
              Nat.beq (Nat.sub c (nat_lit 48))
                (bEnt X (i / 111) (i % 111)))),
            digLanesRun X cs (i + 1), nat_lit 1048576))) := rfl
    rw [e, strictN_eq', nIf_eq', nIf_eq', bAnd_eq', bAnd_eq'] at hi ⊢
    by_cases h10 : ch = '\n'
    · have hb : Nat.beq ch.toNat 10 = true := by rw [h10]; rfl
      rw [if_pos hb] at hi ⊢
      have ef : (ch :: cs).filter (· ≠ '\n') = cs.filter (· ≠ '\n') := by
        rw [List.filter_cons_of_neg (by simp [h10])]
      rw [ef]
      exact ih i hi
    · have hb : ¬ Nat.beq ch.toNat 10 = true := by
        rw [Nat.beq_eq]
        exact fun e => h10 (Char.toNat_inj.1 e)
      rw [if_neg hb] at hi ⊢
      have ef : (ch :: cs).filter (· ≠ '\n') = ch :: cs.filter (· ≠ '\n') := by
        rw [List.filter_cons_of_pos (by simpa using h10)]
      by_cases hd : (Nat.ble 48 ch.toNat && (Nat.ble ch.toNat 57 &&
          Nat.beq (Nat.sub ch.toNat 48) (bEnt X (i / 111) (i % 111)))) = true
      · rw [if_pos hd] at hi ⊢
        obtain ⟨h1, h2⟩ := ih (i + 1) hi
        rw [ef]
        simp only [Bool.and_eq_true, Nat.beq_eq] at hd
        refine ⟨by rw [h1, List.length_cons]; omega, fun k hk => ?_⟩
        rcases k with _ | k
        · simp only [List.getElem_cons_zero, Nat.add_zero]
          have hb48 := hd.1
          simp only [Nat.ble_eq] at hb48
          exact ⟨hb48, hd.2.2⟩
        · simp only [List.getElem_cons_succ]
          obtain ⟨g1, g2⟩ := h2 k (by simpa using hk)
          refine ⟨g1, ?_⟩
          rw [g2]
          congr 2 <;> omega
      · rw [if_neg hd] at hi
        exact absurd rfl hi

theorem digLanesK_sound {cs : List Char} {X n : ℕ} (hn : n < 2 ^ 20) (h : digLanesK cs X n = true) :
    (cs.filter (· ≠ '\n')).length = n ∧ ∀ t < n,
      (cs.filter (· ≠ '\n')).getD t '0' = Char.ofNat (48 + (X / 2 ^ (1332 * (t / 111) + 12 * (t % 111)) % 2 ^ 12)) := by
  have hr : digLanesRun X cs 0 = n := Nat.eq_of_beq_eq_true h
  obtain ⟨h1, h2⟩ := run_spec X cs 0 (by
    rw [hr]; intro e; rw [e] at hn; norm_num at hn)
  rw [hr, Nat.zero_add] at h1
  refine ⟨h1.symm, fun t ht => ?_⟩
  have hk : t < (cs.filter (· ≠ '\n')).length := by omega
  have e2 := h2 t hk
  rw [Nat.zero_add, bEnt_eq] at e2
  obtain ⟨e1, e2⟩ := e2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  have h3 : (cs.filter (· ≠ '\n'))[t].toNat = 48 + X / 2 ^ (1332 * (t / 111) + 12 * (t % 111)) % 2 ^ 12 := by
    omega
  rw [← h3, Char.ofNat_toNat]

end CFSG.KS.LyOm.SB4
end
