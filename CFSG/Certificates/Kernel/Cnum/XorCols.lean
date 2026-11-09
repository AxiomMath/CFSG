module

public import Certificates.Data.CFSGNative.MonsterVis.Act

public section

namespace CFSG.Certificates.Kernel.Cnum

@[expose] def ca (col : Nat → Nat) (v : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | i + 1, acc => ca col v i (if v.testBit i then acc ^^^ col i else acc)

theorem actGo_eq_ca (R : Array Nat) (v : Nat) :
    ∀ n acc, CFSG.Monster.VisCert.Native.actGo R v n acc = ca (fun i => R[i]!) v n acc
  | 0, _ => rfl
  | n + 1, acc => by
    simp only [CFSG.Monster.VisCert.Native.actGo, ca]
    exact actGo_eq_ca R v n _

theorem xor_xor_xor (u v r : Nat) : (u ^^^ r) ^^^ (v ^^^ r) = u ^^^ v := by
  rw [Nat.xor_assoc, Nat.xor_comm r (v ^^^ r), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xor_right_swap (u v r : Nat) : (u ^^^ r) ^^^ v = (u ^^^ v) ^^^ r := by
  rw [Nat.xor_assoc, Nat.xor_comm r v, ← Nat.xor_assoc]

theorem step_xor (p q : Bool) (u v r : Nat) :
    (if (p ^^ q) = true then (u ^^^ v) ^^^ r else u ^^^ v) =
      (if p = true then u ^^^ r else u) ^^^ (if q = true then v ^^^ r else v) := by
  cases p <;> cases q
  · rfl
  · show (u ^^^ v) ^^^ r = u ^^^ (v ^^^ r)
    exact Nat.xor_assoc u v r
  · show (u ^^^ v) ^^^ r = (u ^^^ r) ^^^ v
    exact (xor_right_swap u v r).symm
  · show u ^^^ v = (u ^^^ r) ^^^ (v ^^^ r)
    exact (xor_xor_xor u v r).symm

theorem ca_xor (col : Nat → Nat) :
    ∀ (n a b u v : Nat), ca col (a ^^^ b) n (u ^^^ v) = ca col a n u ^^^ ca col b n v
  | 0, _, _, _, _ => rfl
  | n + 1, a, b, u, v => by
    simp only [ca]
    rw [Nat.testBit_xor, step_xor, ca_xor col n]

theorem ca_xor0 (col : Nat → Nat) (n a b : Nat) : ca col (a ^^^ b) n 0 = ca col a n 0 ^^^ ca col b n 0 := by
  have h := ca_xor col n a b 0 0
  rwa [Nat.xor_zero] at h

theorem foldl_xor (r : Nat → Nat) : ∀ (l : List Nat) (a b u v : Nat),
    l.foldl (fun acc j => if (a ^^^ b).testBit j then acc ^^^ r j else acc) (u ^^^ v) =
      l.foldl (fun acc j => if a.testBit j then acc ^^^ r j else acc) u ^^^
        l.foldl (fun acc j => if b.testBit j then acc ^^^ r j else acc) v
  | [], _, _, _, _ => rfl
  | j :: l, a, b, u, v => by
    simp only [List.foldl_cons]
    rw [Nat.testBit_xor, step_xor, foldl_xor r l]

theorem foldl_xor0 (r : Nat → Nat) (l : List Nat) (a b : Nat) :
    l.foldl (fun acc j => if (a ^^^ b).testBit j then acc ^^^ r j else acc) 0 =
      l.foldl (fun acc j => if a.testBit j then acc ^^^ r j else acc) 0 ^^^
        l.foldl (fun acc j => if b.testBit j then acc ^^^ r j else acc) 0 := by
  have h := foldl_xor r l a b 0 0
  rwa [Nat.xor_zero] at h

theorem all_congr' {α : Type _} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem zero_of_lin {g : Nat → Nat} (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) : g 0 = 0 := by
  have h := hg 0 0
  rw [Nat.xor_zero, Nat.xor_self] at h
  exact h

theorem ca_map (col : Nat → Nat) (v : Nat) {g : Nat → Nat} (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) :
    ∀ n acc, g (ca col v n acc) = ca (fun i => g (col i)) v n (g acc)
  | 0, _ => rfl
  | n + 1, acc => by
    simp only [ca]
    rw [ca_map col v hg n]
    congr 1
    by_cases hb : v.testBit n = true
    · simp [hb, hg]
    · simp [hb]

theorem ca_id : ∀ (n v acc : Nat), ca (fun i => 2 ^ i) v n acc = acc ^^^ v % 2 ^ n
  | 0, v, acc => by simp [ca, Nat.mod_one, Nat.xor_zero]
  | n + 1, v, acc => by
    simp only [ca]
    rw [ca_id n]
    apply Nat.eq_of_testBit_eq
    intro j
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · have h1 : n ≠ j := by omega
      have h2 : j < n + 1 := by omega
      split <;> simp [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, h, h1, h2]
    · split <;> rename_i hb <;> simp [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, hb]
    · have h1 : n ≠ j := by omega
      have h2 : ¬ j < n + 1 := by omega
      have h3 : ¬ j < n := by omega
      split <;> simp [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, h1, h2, h3]

theorem lin_eq {g : Nat → Nat} (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) {n v : Nat} (hv : v < 2 ^ n) :
    g v = ca (fun i => g (2 ^ i)) v n 0 := by
  have h := ca_map (fun i => 2 ^ i) v hg n 0
  rw [ca_id, Nat.zero_xor, Nat.mod_eq_of_lt hv, zero_of_lin hg] at h
  exact h

theorem ca_lt {col : Nat → Nat} {v m : Nat} :
    ∀ (n acc : Nat), (∀ i < n, col i < 2 ^ m) → acc < 2 ^ m → ca col v n acc < 2 ^ m
  | 0, _, _, hacc => hacc
  | n + 1, acc, hcol, hacc => by
    simp only [ca]
    refine ca_lt n _ (fun i hi => hcol i (by omega)) ?_
    split
    · exact Nat.xor_lt_two_pow hacc (hcol n (by omega))
    · exact hacc

end CFSG.Certificates.Kernel.Cnum

end
