module

public import Init

public section

namespace CFSG.KS.Fi22LH

@[expose] def LStep {β : Type} (I Q : β → Prop) : ForInStep β → Prop
  | .yield b => I b
  | .done b => Q b

theorem range'_loop {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) : ∀ (m s : Nat) (b : β),
    (∀ q b, s ≤ q → q < s + m → I q b → LStep (I (q + 1)) Q (f q b)) →
    (∀ b, I (s + m) b → Q b) → I s b → Q (forIn (List.range' s m) b f)
  | 0, s, b, _, hend, h0 => hend b (by simpa using h0)
  | m + 1, s, b, hstep, hend, h0 => by
    rw [List.range'_succ, List.forIn_cons]
    have hs := hstep s b (Nat.le_refl _) (by omega) h0
    cases hf : f s b with
    | done b' =>
      rw [hf] at hs
      exact hs
    | yield b' =>
      rw [hf] at hs
      have e : s + (m + 1) = s + 1 + m := by omega
      exact range'_loop I Q f m (s + 1) b'
        (fun q b h1 h2 h3 => hstep q b (by omega) (by omega) h3)
        (fun b hb => hend b (by rwa [e])) hs

theorem range_loop {β : Type} (I : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → Id (ForInStep β)) (n : Nat) (b : β)
    (hstep : ∀ q b, q < n → I q b → LStep (I (q + 1)) Q (f q b))
    (hend : ∀ b, I n b → Q b) (h0 : I 0 b) : Q (forIn [:n] b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:n] = n := by simp [Std.Legacy.Range.size]
  simp only [hs]
  exact range'_loop I Q f n 0 b (fun q b _ h2 h3 => hstep q b (by omega) h3)
    (fun b hb => hend b (by simpa using hb)) h0

theorem forIn_yield {α β : Type} (f : α → β → Id (ForInStep β)) (g : α → β → β)
    (hf : ∀ a b, f a b = .yield (g a b)) : ∀ (l : List α) (b : β),
    forIn l b f = l.foldl (fun b a => g a b) b
  | [], b => rfl
  | a :: l, b => by
    rw [List.forIn_cons, hf, List.foldl_cons]
    exact forIn_yield f g hf l (g a b)

theorem fold_nonzero (F : Nat → Nat → Nat) (h0 : ∀ i, F i 0 = 0)
    (hmono : ∀ i m, F i m ≠ 0 → m ≤ F i m) : ∀ (l : List Nat) (m : Nat),
    l.foldl (fun m i => F i m) m ≠ 0 → m ≠ 0 ∧ m ≤ l.foldl (fun m i => F i m) m
  | [], m, h => ⟨h, Nat.le_refl _⟩
  | a :: l, m, h => by
    rw [List.foldl_cons] at h ⊢
    obtain ⟨h1, h2⟩ := fold_nonzero F h0 hmono l (F a m) h
    refine ⟨fun e => h1 (by rw [e, h0]), Nat.le_trans (hmono a m h1) h2⟩

end CFSG.KS.Fi22LH
