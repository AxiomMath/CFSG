module

public import Certificates.Data.Kernel.TitsN12K

public section

namespace CFSG.KC.TitsN12Sound

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.TitsN12K

theorem beq_iff (x y : Nat) : Nat.beq x y = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun e => e ▸ Nat.beq_refl x⟩

theorem in2_iff (a b x : Nat) : in2 a b x = true ↔ x = a ∨ x = b := by
  unfold in2
  cases h : Nat.beq x a
  · change Nat.beq x b = true ↔ _
    rw [beq_iff]
    have : x ≠ a := Nat.ne_of_beq_eq_false h
    exact ⟨Or.inr, fun h' => h'.resolve_left this⟩
  · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h), fun _ => rfl⟩

theorem memL_iff (x : Nat) : ∀ L : List Nat, memL x L = true ↔ x ∈ L
  | [] => ⟨fun h => Bool.noConfusion h, fun h => absurd h List.not_mem_nil⟩
  | y :: L => by
    have ih := memL_iff x L
    change bIf(Nat.beq x y, true, memL x L) = true ↔ x ∈ y :: L
    rw [List.mem_cons]
    cases h : Nat.beq x y
    · have : x ≠ y := Nat.ne_of_beq_eq_false h
      change memL x L = true ↔ _
      exact ih.trans ⟨Or.inr, fun h' => h'.resolve_left this⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h), fun _ => rfl⟩

theorem cntAt_eq (LR TR : Nat → Nat) (i a b : Nat) : ∀ C : List Nat,
    cntAt LR TR i a b C = (C.filter fun c => in2 a b (gptC LR TR c i)).length
  | [] => rfl
  | c :: C => by
    have ih := cntAt_eq LR TR i a b C
    change Bool.rec (motive := fun _ => Nat) (cntAt LR TR i a b C)
      (Nat.succ (cntAt LR TR i a b C)) (in2 a b (gptC LR TR c i)) = _
    rw [List.filter_cons]
    cases in2 a b (gptC LR TR c i)
    · exact ih
    · exact congrArg Nat.succ ih

theorem walkK_inv {ok : Nat → Nat → Nat → Bool} {P : Nat → Prop}
    (hok : ∀ c p j, P p → ok c p j = true → P c) :
    ∀ (E : List (Nat × Nat × Nat)) (R : List Nat), (∀ x ∈ R, P x) → ∀ x ∈ walkK ok E R, P x
  | [], R, hR => hR
  | e :: E, R, hR => by
    change ∀ x ∈ Bool.rec (motive := fun _ => List Nat) List.nil (walkK ok E (List.cons e.1 R))
      (bAnd(memL e.2.1 R, ok e.1 e.2.1 e.2.2)), P x
    cases h1 : memL e.2.1 R
    · intro x hx
      exact absurd hx List.not_mem_nil
    · cases h2 : ok e.1 e.2.1 e.2.2
      · intro x hx
        exact absurd hx List.not_mem_nil
      · have hp := hR _ ((memL_iff _ _).1 h1)
        refine walkK_inv hok E (e.1 :: R) fun x hx => ?_
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hok _ _ _ hp h2
        · exact hR x hx

end CFSG.KC.TitsN12Sound

end
