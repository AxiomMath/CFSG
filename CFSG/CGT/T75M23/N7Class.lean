module

public import CFSG.CGT.T75M23.A7Gens

public section

namespace CFSG.CGT.T75M23

open CFSG.CGT.T75JM

@[expose] def modelX7 : Cols := ⟨9, 10, 15, 8⟩

@[expose] def modelY7 : Cols := ⟨2, 6, 10, 3⟩

@[expose] def RelC7 (X Y : Cols) : Prop :=
  compC X X = idC ∧ X ≠ idC ∧ powC Y 5 = idC ∧
    powC (compC X (compC Y (compC X (powC Y 4)))) 3 = idC ∧
    powC (compC (powC Y 4) X) 7 = idC ∧
    compC X (compC Y (compC X (compC (powC (compC Y (compC X (compC (powC Y 4)
      (compC X Y)))) 2) (compC Y (compC X (powC Y 4)))))) = idC

instance (X Y : Cols) : Decidable (RelC7 X Y) := by unfold RelC7; infer_instance

@[expose] def EquivData7 (X Y Q Qi : Cols) : Prop :=
  (∀ i, Q.col i < 16) ∧ (∀ i, Qi.col i < 16) ∧ compC Qi Q = idC ∧ compC Q Qi = idC ∧
    compC X Q = compC Q modelX7 ∧ compC Y Q = compC Q modelY7

@[expose] def EquivC7 (X Y : Cols) : Prop := ∃ Q Qi : Cols, EquivData7 X Y Q Qi

instance (X Y Q Qi : Cols) : Decidable (EquivData7 X Y Q Qi) := by
  unfold EquivData7; infer_instance

theorem EquivData7.left_inv {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Qi (applyC Q v) = v := by
  rw [← applyC_compC, h.2.2.1, applyC_idC hv]

theorem EquivData7.right_inv {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Q (applyC Qi v) = v := by
  rw [← applyC_compC, h.2.2.2.1, applyC_idC hv]

theorem EquivData7.intertwine_x {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) (v : ℕ) :
    applyC X (applyC Q v) = applyC Q (applyC modelX7 v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.1]

theorem EquivData7.intertwine_y {X Y Q Qi : Cols} (h : EquivData7 X Y Q Qi) (v : ℕ) :
    applyC Y (applyC Q v) = applyC Q (applyC modelY7 v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.2]

@[expose] def ModClass7 : Prop :=
  ∀ X Y : Cols, (∀ i, X.col i < 16) → (∀ i, Y.col i < 16) → RelC7 X Y →
    EquivC7 X Y ∨ EquivC7 X (evalC X Y twistWord7)

@[expose] def omega7 : Std.HashMap ℕ (Cols × Cols) :=
  glList.foldl (fun m PPi =>
    m.insert (packPair (compC (compC PPi.1 modelX7) PPi.2) (compC (compC PPi.1 modelY7) PPi.2)) PPi)
    ∅

@[expose] def findQIn7 (m : Std.HashMap ℕ (Cols × Cols)) (X Y : Cols) : Bool :=
  match m.get? (packPair X Y) with
  | some (Q, Qi) => decide (EquivData7 X Y Q Qi)
  | none => false

@[expose] def findQ7 (X Y : Cols) : Bool := findQIn7 omega7 X Y

theorem findQIn7_sound {m : Std.HashMap ℕ (Cols × Cols)} {X Y : Cols}
    (h : findQIn7 m X Y = true) : EquivC7 X Y := by
  unfold findQIn7 at h
  split at h
  · rename_i Q Qi _
    exact ⟨Q, Qi, of_decide_eq_true h⟩
  · exact absurd h (by simp)

theorem findQ7_sound {X Y : Cols} (h : findQ7 X Y = true) : EquivC7 X Y := findQIn7_sound h

@[expose] def goodPair7 (X Y : Cols) : Bool :=
  findQ7 X Y || findQ7 X (evalC X Y twistWord7)

theorem goodPair7_sound {X Y : Cols} (h : goodPair7 X Y = true) :
    EquivC7 X Y ∨ EquivC7 X (evalC X Y twistWord7) := by
  unfold goodPair7 at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl (findQ7_sound h)
  · exact Or.inr (findQ7_sound h)

@[expose] def ord5List : List ℕ :=
  (List.range 65536).filter fun n => decide (powC (unpackC n) 5 = idC)

@[noinline, expose] def modClassCheck7 : Bool :=
  (List.range 65536).all fun m =>
    let X := unpackC m
    !decide (compC X X = idC ∧ X ≠ idC) ||
      ord5List.all fun n =>
        let Y := unpackC n
        !decide (RelC7 X Y) || goodPair7 X Y

theorem modClass7_of_check (h : modClassCheck7 = true) : ModClass7 := by
  intro X Y hX hY hrel
  unfold modClassCheck7 at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  have h1 := h (packC X) (packC_lt hX)
  rw [unpackC_packC hX] at h1
  rcases h1 with h1 | h1
  · exact absurd ⟨hrel.1, hrel.2.1⟩ h1
  · have hm : packC Y ∈ ord5List := by
      simp only [ord5List, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨packC_lt hY, by rw [unpackC_packC hY]; exact hrel.2.2.1⟩
    have h2 := h1 (packC Y) hm
    rw [unpackC_packC hY] at h2
    rcases h2 with h2 | h2
    · exact absurd hrel h2
    · exact goodPair7_sound h2

end CFSG.CGT.T75M23
