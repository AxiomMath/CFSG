module

public import Certificates.Data.Kernel.J4Count
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Group.Nat.Defs

public section

namespace CFSG.KC.J4Count

theorem combo_nil (m : Nat) : combo [] m = 0 := rfl

theorem combo_cons (b : Nat) (B : List Nat) (m : Nat) :
    combo (b :: B) m = (if m.testBit 0 then b else 0) ^^^ combo B (m >>> 1) := by
  change Nat.xor (Bool.rec (motive := fun _ => Nat) 0 b (Nat.testBit m 0)) (combo B (m >>> 1)) = _
  cases m.testBit 0 <;> rfl

theorem decode_nil (a : Nat) : decode [] a = 0 := rfl

theorem decode_cons (p : Nat) (P : List Nat) (a : Nat) :
    decode (p :: P) a = (if a.testBit p then 1 else 0) + 2 * decode P a := by
  change Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.testBit a p)) (Nat.mul 2 (decode P a)) = _
  cases a.testBit p <;> rfl

theorem combo_mem {S : Nat → Prop} (h0 : S 0) (hx : ∀ a b, S a → S b → S (a ^^^ b)) :
    ∀ {B : List Nat}, (∀ b ∈ B, S b) → ∀ m, S (combo B m)
  | [], _, m => by rw [combo_nil]; exact h0
  | b :: B, hB, m => by
    rw [combo_cons]
    refine hx _ _ ?_ (combo_mem h0 hx (fun x hx' => hB x (List.mem_cons_of_mem _ hx')) _)
    split_ifs
    · exact hB b List.mem_cons_self
    · exact h0

theorem combo_lt {k : Nat} {B : List Nat} (hB : ∀ b ∈ B, b < 2 ^ k) (m : Nat) :
    combo B m < 2 ^ k :=
  combo_mem (S := fun a => a < 2 ^ k) (Nat.two_pow_pos k) (fun a b ha hb => Nat.xor_lt_two_pow ha hb)
    hB m

theorem decode_lt : ∀ (P : List Nat) (a : Nat), decode P a < 2 ^ P.length
  | [], a => by rw [decode_nil]; exact Nat.two_pow_pos 0
  | p :: P, a => by
    rw [decode_cons, List.length_cons, pow_succ]
    have := decode_lt P a
    split_ifs <;> omega

variable {B P : List Nat}

theorem mem_image_iff (hlen : P.length = B.length)
    (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) (a : Nat) :
    (∃ m < 2 ^ B.length, combo B m = a) ↔ combo B (decode P a) = a := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [hinv m hm]
  · intro h
    exact ⟨decode P a, hlen ▸ decode_lt P a, h⟩

theorem card_image (hinv : ∀ m < 2 ^ B.length, decode P (combo B m) = m) :
    ((Finset.range (2 ^ B.length)).image (combo B)).card = 2 ^ B.length := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro m hm m' hm' e
  have h1 := hinv m (Finset.mem_range.1 hm)
  have h2 := hinv m' (Finset.mem_range.1 hm')
  rw [← h1, ← h2]
  exact congrArg (decode P) e

end CFSG.KC.J4Count

end
