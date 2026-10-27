module

public import Certificates.Data.Kernel.Spor.PSlp

public section

namespace CFSG.KS.PSlp

open CFSG.KC.Enum CFSG.KS CFSG.KC.PSlp

theorem letLP_val (y : Nat) (k : Nat → List Nat) : letLP y k = k y := by
  cases y <;> rfl

theorem strictN_val (y : Nat) (k : Nat → Nat) : CFSG.KC.Loop.strictN y k = k y := by
  cases y <;> rfl

theorem nthD_mem : ∀ (l : List Nat) (i d : Nat), nthD l i d ∈ l ∨ nthD l i d = d
  | [], _, _ => Or.inr rfl
  | x :: l, 0, d => Or.inl List.mem_cons_self
  | x :: l, i + 1, d => by
    have e : nthD (x :: l) (i + 1) d = nthD l i d := rfl
    rw [e]
    rcases nthD_mem l i d with h | h
    · exact Or.inl (List.mem_cons_of_mem x h)
    · exact Or.inr h

variable {n w fw d : Nat} {Good : Nat → Prop}

theorem nthD_good (hd : Good d) {l : List Nat} (hl : ∀ X ∈ l, Good X) (i : Nat) :
    Good (nthD l i d) := by
  rcases nthD_mem l i d with h | h
  · exact hl _ h
  · rw [h]
    exact hd

theorem slpGo_succ (c P : Nat) (acc : List Nat) :
    slpGo n w fw d (c + 1) P acc = slpGo n w fw d c (Nat.shiftRight P (Nat.add fw fw))
      (pcomp n w (mask w) (nthD acc fld(P, nat_lit 0, mask fw) d)
        (nthD acc fld(P, fw, mask fw) d) :: acc) := by
  change letLP (stepP n w d acc fld(P, nat_lit 0, mask fw) fld(P, fw, mask fw)) (fun y =>
    letLP (Nat.shiftRight P (Nat.add fw fw)) fun P' => slpGo n w fw d c P' (List.cons y acc)) = _
  rw [letLP_val, letLP_val, stepP, strictN_val, strictN_val]

theorem slpGo_good (hd : Good d)
    (hmul : ∀ X Y, Good X → Good Y → Good (pcomp n w (mask w) X Y)) :
    ∀ (c P : Nat) (acc : List Nat), (∀ X ∈ acc, Good X) → ∀ X ∈ slpGo n w fw d c P acc, Good X
  | 0, _, _, h => h
  | c + 1, P, acc, h => by
    rw [slpGo_succ]
    refine slpGo_good hd hmul c _ _ fun X hX => ?_
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hmul _ _ (nthD_good hd h _) (nthD_good hd h _)
    · exact h X hX

end CFSG.KS.PSlp

end
