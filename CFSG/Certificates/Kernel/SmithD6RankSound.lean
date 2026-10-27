module

public import Certificates.Data.Kernel.SmithD6.RankCheck
import CFSG.Certificates.Kernel.SmithD6WtSound
public import CFSG.Certificates.Kernel.KeyTreeChunksSound

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem kcDist_eq (c : Nat) :
    (if c == 1 then 3 else if c == 4 then 2 else if c == 16 then 1 else 0) = kcDist c := by
  unfold kcDist
  by_cases h1 : c = 1
  · subst h1
    rfl
  by_cases h4 : c = 4
  · subst h4
    rfl
  by_cases h16 : c = 16
  · subst h16
    rfl
  have b1 : Nat.beq c 1 = false := beq_false h1
  have b4 : Nat.beq c 4 = false := beq_false h4
  have b16 : Nat.beq c 16 = false := beq_false h16
  rw [b1, b4, b16]
  simp [h1, h4, h16]

@[expose] noncomputable def rankTerm (R i j v : Nat) : Nat :=
  if R.testBit (kcDist (d6MeetK i j)) then v else 0

theorem rankTerm_eq (R i j v : Nat) :
    nIf(Nat.beq (fld(R, kcDist (d6MeetK i j), 1)) 1, v, 0) = rankTerm R i j v := by
  unfold rankTerm
  rw [fld_one_eq]
  cases R.testBit (kcDist (d6MeetK i j)) <;> rfl

theorem foldl_rankRow (R i : Nat) : ∀ (cc inv : List Nat) (a : Nat), cc.length = inv.length →
    (List.range cc.length).foldl (fun acc t => acc ^^^ rankTerm R i (cc.getD t 0) (inv.getD t 0)) a =
      a ^^^ d6RankRow R i cc inv
  | [], _, a, _ => by
    change _ = a ^^^ 0
    simp
  | _ :: _, [], _, h => absurd h (by simp)
  | j :: cc, v :: inv, a, h => by
    change _ = a ^^^ Nat.xor (nIf(Nat.beq (fld(R, kcDist (d6MeetK i j), 1)) 1, v, 0))
      (d6RankRow R i cc inv)
    rw [rankTerm_eq, List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [foldl_rankRow R i cc inv _ (by simpa using h)]
    change _ ^^^ _ = a ^^^ (_ ^^^ _)
    rw [Nat.xor_assoc]

theorem d6RankRow_eq (R i : Nat) {cc inv : List Nat} (h : cc.length = inv.length) :
    d6RankRow R i cc inv =
      (List.range cc.length).foldl
        (fun acc t => acc ^^^ rankTerm R i (cc.getD t 0) (inv.getD t 0)) 0 := by
  rw [foldl_rankRow R i cc inv 0 h, Nat.zero_xor]

theorem testBit_foldl_xor (a : Nat → Bool) (g : Nat → Nat) (u : Nat) : ∀ n,
    ((List.range n).foldl (fun acc t => acc ^^^ (if a t then g t else 0)) 0).testBit u =
      (List.range n).foldl (fun acc t => acc ^^ (a t && (g t).testBit u)) false
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_cons,
      List.foldl_nil, List.foldl_nil, Nat.testBit_xor, testBit_foldl_xor a g u n]
    cases a n <;> simp

theorem d6RankGo_sound {R : Nat} {cc inv : List Nat} : ∀ (rr : List Nat) (s : Nat),
    d6RankGo R cc inv rr s = true → ∀ k < rr.length, d6RankRow R (rr.getD k 0) cc inv = 2 ^ (s + k)
  | [], _, _, _, hk => absurd hk (by simp)
  | i :: rr, s, h, k, hk => by
    change bAnd(Nat.beq (d6RankRow R i cc inv) (Nat.pow 2 s), d6RankGo R cc inv rr (Nat.succ s)) =
      true at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases k with _ | k
    · rw [Nat.add_zero, List.getD_cons_zero]
      exact Nat.eq_of_beq_eq_true h1
    · have e : s + (k + 1) = Nat.succ s + k := by omega
      rw [List.getD_cons_succ, e]
      exact d6RankGo_sound rr (Nat.succ s) h2 k (by simpa using hk)

end CFSG.KD.SmithD6

end
