module

public import CFSG.Certificates.Kernel.Fi23K.EqSound

public section

namespace CFSG.KC.Fi23K

@[expose] def exW (rhs : Nat → Option (List Nat)) : Nat → List Nat → List Nat
  | 0, w => w
  | f + 1, w => w.flatMap fun r => match rhs r with
    | some u => exW rhs f u
    | none => [r]

variable {G : Nat → Nat} {nr : Nat}

theorem wv_lt (hrng : ∀ r < nr, ∀ x < 31671, tb G r x < 31671) :
    ∀ (w : List Nat), (∀ r ∈ w, r < nr) → ∀ x < 31671, wv G w x < 31671
  | [], _, x, hx => hx
  | r :: w, hw, x, hx => by
    rw [wv_cons]
    exact hrng r (hw r List.mem_cons_self) _
      (wv_lt hrng w (fun s hs => hw s (List.mem_cons_of_mem r hs)) x hx)

theorem exW_eq (hrng : ∀ r < nr, ∀ x < 31671, tb G r x < 31671) {rhs : Nat → Option (List Nat)}
    (hrhs : ∀ r u, rhs r = some u → (∀ s ∈ u, s < nr) ∧ ∀ x < 31671, tb G r x = wv G u x) :
    ∀ f (w : List Nat), (∀ r ∈ w, r < nr) → ∀ x < 31671, wv G w x = wv G (exW rhs f w) x
  | 0, w, _, x, _ => rfl
  | f + 1, [], _, x, _ => rfl
  | f + 1, r :: w, hw, x, hx => by
    have hw' : ∀ s ∈ w, s < nr := fun s hs => hw s (List.mem_cons_of_mem r hs)
    have ih := exW_eq hrng hrhs (f + 1) w hw' x hx
    have e : exW rhs (f + 1) (r :: w) = (match rhs r with
        | some u => exW rhs f u
        | none => [r]) ++ exW rhs (f + 1) w := by
      simp only [exW, List.flatMap_cons]
    rw [e, wv_append, wv_cons, ← ih]
    have hy := wv_lt hrng w hw' x hx
    cases h : rhs r with
    | none => rfl
    | some u =>
      obtain ⟨hu, hv⟩ := hrhs r u h
      simp only
      rw [hv _ hy]
      exact exW_eq hrng hrhs f u hu _ hy

end CFSG.KC.Fi23K

end
