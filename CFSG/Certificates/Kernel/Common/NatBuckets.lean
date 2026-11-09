module

public section

namespace CFSG.KC.NatBuckets

theorem beqN (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · have : a ≠ b := fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h
    simpa using this
  · simpa using Nat.eq_of_beq_eq_true h

@[expose] noncomputable def memN (l : List Nat) (x : Nat) : Bool := l.any fun a => Nat.beq x a

@[expose] noncomputable def memB (B : List (List Nat)) (y : Nat) : Bool := memN (B.getD (Nat.mod y 37) []) y

@[expose] noncomputable def insB (B : List (List Nat)) (y : Nat) : List (List Nat) :=
  B.set (Nat.mod y 37) (y :: B.getD (Nat.mod y 37) [])

@[expose] noncomputable def bucketsOf (l : List Nat) : List (List Nat) := l.foldl insB (List.replicate 37 [])

theorem beq_comm' (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  rw [← beqN, ← beqN, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact eq_comm

theorem getD_set' (l : List (List Nat)) {n : Nat} (m : Nat) (a : List Nat) (h : n < l.length) :
    (l.set n a).getD m [] = if n = m then a else l.getD m [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set]
  split <;> simp_all

theorem insB_length (B : List (List Nat)) (y : Nat) : (insB B y).length = B.length :=
  List.length_set ..

theorem memB_insB {B : List (List Nat)} (hB : B.length = 37) (y z : Nat) :
    memB (insB B y) z = (Nat.beq z y || memB B z) := by
  unfold memB insB
  have hy : Nat.mod y 37 < B.length := by rw [hB]; exact Nat.mod_lt _ (by decide)
  rw [getD_set' B _ _ hy]
  by_cases hm : Nat.mod y 37 = Nat.mod z 37
  · rw [if_pos hm, memN, List.any_cons, ← memN, hm]
  · rw [if_neg hm]
    have : Nat.beq z y = false := by
      cases h : Nat.beq z y
      · rfl
      · exact absurd (by rw [Nat.eq_of_beq_eq_true h]) hm
    rw [this, Bool.false_or]

theorem memB_replicate (z : Nat) : memB (List.replicate 37 []) z = false := by
  unfold memB
  have : Nat.mod z 37 < 37 := Nat.mod_lt _ (by decide)
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos this]
  rfl

theorem memB_bucketsOf_aux : ∀ (l : List Nat) (B : List (List Nat)), B.length = 37 →
    ∀ z, memB (l.foldl insB B) z = (memN l z || memB B z)
  | [], _, _, z => by simp [memN]
  | a :: l, B, hB, z => by
    rw [List.foldl_cons, memB_bucketsOf_aux l _ (by rw [insB_length, hB]), memB_insB hB]
    simp only [memN, List.any_cons]
    cases Nat.beq z a <;> cases l.any (fun a => Nat.beq z a) <;> cases memB B z <;> rfl

theorem memN_eq_memB (l : List Nat) (z : Nat) : memN l z = memB (bucketsOf l) z := by
  rw [bucketsOf, memB_bucketsOf_aux l _ (List.length_replicate ..), memB_replicate, Bool.or_false]

end CFSG.KC.NatBuckets
