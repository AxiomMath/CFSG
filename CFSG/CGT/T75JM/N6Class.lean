module

public import CFSG.CGT.T75JM.N6Cols
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.CGT.T75JM

@[expose] def modelX : Cols := ⟨1, 11, 12, 8⟩

@[expose] def modelY : Cols := ⟨10, 4, 5, 9⟩

@[expose] def evalC (X Y : Cols) : List ℕ → Cols
  | [] => idC
  | l :: w => compC (if l = 0 then X else Y) (evalC X Y w)

@[expose] def RelC (X Y : Cols) : Prop :=
  compC X X = idC ∧ X ≠ idC ∧ powC Y 4 = idC ∧ powC (compC X Y) 5 = idC ∧
    powC (compC X (compC Y Y)) 5 = idC

instance (X Y : Cols) : Decidable (RelC X Y) := by unfold RelC; infer_instance

@[expose] def twistWord : List ℕ := [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0]

@[expose] def EquivData (X Y Q Qi : Cols) : Prop :=
  (∀ i, Q.col i < 16) ∧ (∀ i, Qi.col i < 16) ∧ compC Qi Q = idC ∧ compC Q Qi = idC ∧
    compC X Q = compC Q modelX ∧ compC Y Q = compC Q modelY

@[expose] def EquivC (X Y : Cols) : Prop := ∃ Q Qi : Cols, EquivData X Y Q Qi

instance (X Y Q Qi : Cols) : Decidable (EquivData X Y Q Qi) := by
  unfold EquivData; infer_instance

theorem EquivData.left_inv {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Qi (applyC Q v) = v := by
  rw [← applyC_compC, h.2.2.1, applyC_idC hv]

theorem EquivData.right_inv {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) {v : ℕ} (hv : v < 16) :
    applyC Q (applyC Qi v) = v := by
  rw [← applyC_compC, h.2.2.2.1, applyC_idC hv]

theorem EquivData.intertwine_x {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) (v : ℕ) :
    applyC X (applyC Q v) = applyC Q (applyC modelX v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.1]

theorem EquivData.intertwine_y {X Y Q Qi : Cols} (h : EquivData X Y Q Qi) (v : ℕ) :
    applyC Y (applyC Q v) = applyC Q (applyC modelY v) := by
  rw [← applyC_compC, ← applyC_compC, h.2.2.2.2.2]

@[expose] def ModClass : Prop :=
  ∀ X Y : Cols, (∀ i, X.col i < 16) → (∀ i, Y.col i < 16) → RelC X Y →
    EquivC X Y ∨ EquivC X (evalC X Y twistWord)

@[expose] def packC (c : Cols) : ℕ := c.c0 + 16 * c.c1 + 256 * c.c2 + 4096 * c.c3

@[expose] def unpackC (m : ℕ) : Cols := ⟨m % 16, m / 16 % 16, m / 256 % 16, m / 4096 % 16⟩

@[expose] def invByScan (P : Cols) : Cols :=
  let f : ℕ → ℕ := fun b => ((List.range 16).find? (fun v => applyC P v == b)).getD 0
  ⟨f 1, f 2, f 4, f 8⟩

@[expose] def glList : List (Cols × Cols) :=
  (List.range 65536).filterMap fun m =>
    let P := unpackC m
    let Pi := invByScan P
    if compC P Pi = idC ∧ compC Pi P = idC then some (P, Pi) else none

@[expose] def packPair (X Y : Cols) : ℕ := packC X + 65536 * packC Y

@[expose] def omega1 : Std.HashMap ℕ (Cols × Cols) :=
  glList.foldl (fun m PPi =>
    m.insert (packPair (compC (compC PPi.1 modelX) PPi.2) (compC (compC PPi.1 modelY) PPi.2)) PPi)
    ∅

@[expose] def findQIn (m : Std.HashMap ℕ (Cols × Cols)) (X Y : Cols) : Bool :=
  match m.get? (packPair X Y) with
  | some (Q, Qi) => decide (EquivData X Y Q Qi)
  | none => false

@[expose] def findQ (X Y : Cols) : Bool := findQIn omega1 X Y

theorem findQIn_sound {m : Std.HashMap ℕ (Cols × Cols)} {X Y : Cols}
    (h : findQIn m X Y = true) : EquivC X Y := by
  unfold findQIn at h
  split at h
  · rename_i Q Qi _
    exact ⟨Q, Qi, of_decide_eq_true h⟩
  · exact absurd h (by simp)

theorem findQ_sound {X Y : Cols} (h : findQ X Y = true) : EquivC X Y := findQIn_sound h

@[expose] def goodPair (X Y : Cols) : Bool := findQ X Y || findQ X (evalC X Y twistWord)

theorem goodPair_sound {X Y : Cols} (h : goodPair X Y = true) :
    EquivC X Y ∨ EquivC X (evalC X Y twistWord) := by
  unfold goodPair at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact Or.inl (findQ_sound h)
  · exact Or.inr (findQ_sound h)

@[expose] def ord4List : List ℕ :=
  (List.range 65536).filter fun n => decide (powC (unpackC n) 4 = idC)

@[noinline, expose] def modClassCheck : Bool :=
  (List.range 65536).all fun m =>
    let X := unpackC m
    !decide (compC X X = idC ∧ X ≠ idC) ||
      ord4List.all fun n =>
        let Y := unpackC n
        !decide (RelC X Y) || goodPair X Y

theorem packC_lt {c : Cols} (hc : ∀ i, c.col i < 16) : packC c < 65536 := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  unfold packC; omega

theorem unpackC_packC {c : Cols} (hc : ∀ i, c.col i < 16) : unpackC (packC c) = c := by
  have h0 := hc 0; have h1 := hc 1; have h2 := hc 2; have h3 := hc 3
  simp only [Cols.col] at h0 h1 h2 h3
  obtain ⟨a, b, c', d⟩ := c
  simp only [unpackC, packC, Cols.mk.injEq] at h0 h1 h2 h3 ⊢
  omega

theorem modClass_of_check (h : modClassCheck = true) : ModClass := by
  intro X Y hX hY hrel
  unfold modClassCheck at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  have h1 := h (packC X) (packC_lt hX)
  rw [unpackC_packC hX] at h1
  rcases h1 with h1 | h1
  · exact absurd ⟨hrel.1, hrel.2.1⟩ h1
  · have hm : packC Y ∈ ord4List := by
      simp only [ord4List, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨packC_lt hY, by rw [unpackC_packC hY]; exact hrel.2.2.1⟩
    have h2 := h1 (packC Y) hm
    rw [unpackC_packC hY] at h2
    rcases h2 with h2 | h2
    · exact absurd hrel h2
    · exact goodPair_sound h2

end CFSG.CGT.T75JM
