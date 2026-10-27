module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS

open CFSG.KC.Enum

theorem bAnd_iff (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = true ↔
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp

theorem allBlk_spec {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, allBlk b f len = true →
    ∀ l < len, f (Nat.add b l) = true
  | 0, _, l, hl => absurd hl (Nat.not_lt_zero l)
  | len + 1, h, l, hl => by
    have h' : Bool.rec (motive := fun _ => Bool) false (allBlk b f len) (f (Nat.add b len)) =
      true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases Nat.lt_or_ge l len with hll | hll
    · exact allBlk_spec h2 l hll
    · have : l = len := by omega
      subst this
      exact h1

theorem rec_blocks_spec {f : Nat → Bool} : ∀ {q : Nat},
    Nat.rec (motive := fun _ => Bool) true
      (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
        (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q = true →
    ∀ h < q, allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64) = true
  | 0, _, h, hh => absurd hh (Nat.not_lt_zero h)
  | q + 1, hr, h, hh => by
    have hr' : Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) q)
      (allBlk (Nat.shiftLeft q (nat_lit 6)) f (nat_lit 64)) = true := hr
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hr'
    rcases Nat.lt_or_ge h q with hq | hq
    · exact rec_blocks_spec h2 h hq
    · have : h = q := by omega
      subst this
      exact h1

theorem allN_spec {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  intro i hi
  have h' : Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true
        (fun h ih => Bool.rec (motive := fun _ => Bool) false ih
          (allBlk (Nat.shiftLeft h (nat_lit 6)) f (nat_lit 64))) (Nat.shiftRight n (nat_lit 6)))
      (allBlk (Nat.shiftLeft (Nat.shiftRight n (nat_lit 6)) (nat_lit 6)) f
        (Nat.land n (nat_lit 63))) = true := h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  have e6 : ∀ x : Nat, Nat.shiftLeft x (nat_lit 6) = x * 64 := fun x => by
    change x <<< 6 = x * 64
    rw [Nat.shiftLeft_eq]
  have e64 : Nat.shiftRight n (nat_lit 6) = n / 64 := by
    change n >>> 6 = n / 64
    rw [Nat.shiftRight_eq_div_pow]
  have er : Nat.land n (nat_lit 63) = n % 64 := by
    change n &&& (2 ^ 6 - 1) = n % 2 ^ 6
    exact Nat.and_two_pow_sub_one_eq_mod n 6
  have hi' : i = Nat.add (i / 64 * 64) (i % 64) := by
    simp only [Nat.add_eq]
    omega
  rcases Nat.lt_or_ge (i / 64) (n / 64) with hq | hq
  · have hb := rec_blocks_spec h2 (i / 64) (by rw [e64]; exact hq)
    rw [e6] at hb
    rw [hi']
    exact allBlk_spec hb (i % 64) (Nat.mod_lt i (by omega))
  · have hq' : i / 64 = n / 64 := by
      have : i / 64 ≤ n / 64 := Nat.div_le_div_right (Nat.le_of_lt hi)
      omega
    rw [e64, er, e6] at h1
    rw [hi', hq']
    exact allBlk_spec h1 (i % 64) (by omega)

end CFSG.KS

end
