module

public import Certificates.Data.Kernel.Misc.Oq
public import Certificates.Data.Kernel.Misc.Base
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
import CFSG.Certificates.Kernel.Misc.OqValidSound
import CFSG.Certificates.Kernel.Misc.OqSearchSound
import CFSG.Certificates.Kernel.Misc.OqCertSound
import CFSG.Certificates.Kernel.Misc.OqElemSound
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] def b2n (u : Bool) : Nat := if u then 1 else 0

theorem search2K_sound (u : Bool) {t : ℕ} (ht : t < 64) :
    (search2K (b2n u) t).map unpack6 = oqFrom u t :=
  search2K_sound' u ht

theorem sortedK_sound {L : List ℕ} (h : sortedK L = true) :
    strictSorted (L.map fun x => codeT (unpack6 x)) = true :=
  sortedK_sound' h

theorem validK_sound (u : Bool) {P : ℕ} (h : validK (b2n u) P = true) :
    validT u (unpack6 P) = true :=
  validK_sound' u h

theorem sgnK_sound (u : Bool) {P : ℕ} (h : sgnK (b2n u) P = true) :
    sgnOK u (unpack6 P) = true :=
  sgnK_sound' u h

theorem certK_sound (u : Bool) {P : ℕ} {ws : List (List ℕ)} {v w : ℕ}
    (hws : ∀ x ∈ ws, ∀ a ∈ x, a < 4) (h : certK (b2n u) P ws v w = true) : validCert u (unpack6 P) (ws, v, w) = true :=
  certK_sound' u hws h

theorem conjK_sound {P r : ℕ} {w : List ℕ} (h : conjK P r w = true) :
    (∀ a ∈ w, a < 3) ∧
      compT (evalW (unpack6 P) w) (unpack6 P) = compT (unpack6 r) (evalW (unpack6 P) w) :=
  conjK_sound' h

theorem elem_sound (u : Bool) {R S BR I : List ℕ} (hinv : invsK (b2n u) R BR = true)
    (h : ∀ s ∈ S, elemT (b2n u) (rtK R BR) I (tabK s) (bOfK (b2n u) s) = true) :
    ∀ r ∈ R, ∀ s ∈ S,
      (u = true → bMul (bOf u (unpack6 r)) (bOf u (unpack6 s)) = idE →
        compT (unpack6 r) (unpack6 s) = idT ∨ compT (unpack6 r) (unpack6 s) = omT ∨
          compT (unpack6 r) (unpack6 s) = compT omT omT) ∧
      (isInvT (compT (unpack6 r) (unpack6 s)) = true →
        presT u (compT (unpack6 r) (unpack6 s)) = true →
          compT (unpack6 r) (unpack6 s) ∈ I.map unpack6) :=
  elem_sound' u hinv h

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB]

theorem notB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem allL_iff' {L : List ℕ} {f : ℕ → Bool} : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx List.not_mem_nil, fun _ => rfl⟩
  | cons x t ih =>
    change andB (f x) (allL t f) = true ↔ _
    rw [andB_iff, ih, List.forall_mem_cons]

theorem allN_iff' {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i, i < m → f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih, Nat.forall_lt_succ_right, and_comm]

theorem memK_iff {x : ℕ} {L : List ℕ} : memK x L = true ↔ x ∈ L := by
  induction L with
  | nil =>
    refine ⟨fun h => ?_, fun h => absurd h List.not_mem_nil⟩
    change false = true at h
    exact absurd h (by decide)
  | cons y t ih =>
    change orB (Nat.beq y x) (memK x t) = true ↔ _
    rw [List.mem_cons, ← ih]
    cases h : Nat.beq y x
    · have hne : x ≠ y := fun e => Nat.ne_of_beq_eq_false h e.symm
      change memK x t = true ↔ _
      simp [hne]
    · have he : x = y := (Nat.eq_of_beq_eq_true h).symm
      change true = true ↔ _
      simp [he]

theorem nodupK_sound {L : List ℕ} (h : nodupK L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons x t ih =>
    change andB (notB (memK x t)) (nodupK t) = true at h
    rw [andB_iff, notB_iff] at h
    refine List.nodup_cons.2 ⟨fun hx => ?_, ih h.2⟩
    rw [← memK_iff, h.1] at hx
    exact absurd hx (by decide)

theorem isNilK_iff {α : Type} {L : List α} : isNilK L = true ↔ L = [] := by
  cases L with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x t =>
    refine ⟨fun h => ?_, fun h => absurd h (List.cons_ne_nil x t)⟩
    change false = true at h
    exact absurd h (by decide)

theorem eqLN_sound {a b : List ℕ} (h : eqLN a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons _ _ =>
      change false = true at h
      exact absurd h (by decide)
  | cons x t ih =>
    cases b with
    | nil =>
      change false = true at h
      exact absurd h (by decide)
    | cons y s =>
      change andB (Nat.beq x y) (eqLN t s) = true at h
      rw [andB_iff] at h
      rw [Nat.eq_of_beq_eq_true h.1, ih h.2]

theorem lenK_eq (L : List ℕ) : lenK L = L.length := by
  induction L with
  | nil => rfl
  | cons _ t ih =>
    change Nat.succ (lenK t) = _
    rw [ih]
    rfl

theorem dropK_eq {α : Type} (a : ℕ) (L : List α) : dropK a L = L.drop a := by
  induction a generalizing L with
  | zero => rfl
  | succ a ih =>
    change dropK a (List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) L) = _
    cases L with
    | nil =>
      rw [List.drop_nil]
      exact (ih []).trans List.drop_nil
    | cons x t => exact ih t

theorem takeK_eq {α : Type} (n : ℕ) (L : List α) : takeK n L = L.take n := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    cases L with
    | nil => rfl
    | cons x t =>
      change List.cons x (takeK n t) = _
      rw [ih]
      rfl

theorem getK_eq (L : List ℕ) (k : ℕ) : getK L k = L.getD k 0 := by
  have h : ∀ M : List ℕ, List.rec (motive := fun _ => ℕ) 0 (fun x _ _ => x) M = M.headD 0 := by
    intro M
    cases M <;> rfl
  rw [getK, h, dropK_eq]
  cases L <;> cases k <;> simp

theorem fstIK_eq (D : List (ℕ × List ℕ × ℕ)) : fstIK D = D.map Prod.fst := by
  induction D with
  | nil => rfl
  | cons e t ih =>
    change List.cons e.1 (fstIK t) = _
    rw [ih]
    rfl

theorem fld6_zero (r : ℕ) : fld6 r 0 = r % 64 := by
  have h : fld6 r 0 = r &&& (2 ^ 6 - 1) := rfl
  rw [h, Nat.and_two_pow_sub_one_eq_mod]

theorem headK_eq (R : List ℕ) : headK R = R.map (· % 64) := by
  induction R with
  | nil => rfl
  | cons r t ih =>
    change List.cons (fld6 r 0) (headK t) = _
    rw [ih, fld6_zero]
    rfl

theorem appK_eq {α : Type} (l₁ l₂ : List α) : appK l₁ l₂ = l₁ ++ l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a t ih =>
    change List.cons a (appK t l₂) = _
    rw [ih]
    rfl

theorem level2K_append (u k : ℕ) (A B : List (ℕ × List ℕ × List ℕ)) :
    level2K u k (A ++ B) = level2K u k A ++ level2K u k B := by
  induction A with
  | nil => rfl
  | cons st t ih =>
    change appK (step2K u k st) (level2K u k (t ++ B)) =
      appK (step2K u k st) (level2K u k t) ++ level2K u k B
    rw [appK_eq, appK_eq, ih, List.append_assoc]

theorem fstsK_append (A B : List (ℕ × List ℕ × List ℕ)) :
    fstsK (A ++ B) = fstsK A ++ fstsK B := by
  induction A with
  | nil => rfl
  | cons st t ih =>
    change List.cons st.1 (fstsK (t ++ B)) = List.cons st.1 (fstsK t) ++ fstsK B
    rw [ih]
    rfl

theorem levels2K_four (u : ℕ) (L : List (ℕ × List ℕ × List ℕ)) :
    levels2K u 4 L = level2K u 5 (level2K u 4 L) := rfl

theorem search2K_one (u : ℕ) : search2K u 1 = fstsK (levels2K u 4 (lev3K u)) := rfl

theorem fin_append (u : ℕ) (A B : List (ℕ × List ℕ × List ℕ)) :
    fstsK (levels2K u 4 (A ++ B)) = fstsK (levels2K u 4 A) ++ fstsK (levels2K u 4 B) := by
  rw [levels2K_four, levels2K_four, levels2K_four, level2K_append, level2K_append, fstsK_append]

theorem drop_split {α : Type} (L : List α) (a n : ℕ) :
    L.drop a = takeK n (dropK a L) ++ L.drop (a + n) := by
  rw [takeK_eq, dropK_eq, ← List.drop_drop, List.take_append_drop]

theorem badK_sound (u : Bool) {R : List ℕ} (h : badK (b2n u) R = true) {t : ℕ} (ht : t < 64)
    (hR : ∀ r ∈ R, r % 64 ≠ t) : oqFrom u t = [] := by
  have h1 : impB (notB (memK t (headK R))) (isNilK (search2K (b2n u) t)) = true :=
    allN_iff'.1 h t ht
  rw [impB_iff, notB_iff] at h1
  have h2 : memK t (headK R) = false := by
    cases hm : memK t (headK R)
    · rfl
    · rw [memK_iff, headK_eq] at hm
      obtain ⟨r, hr, hrt⟩ := List.mem_map.1 hm
      exact absurd hrt (hR r hr)
  rw [← search2K_sound u ht, isNilK_iff.1 (h1 h2), List.map_nil]

theorem conjsK_sound {KR : List ℕ} {D : List (ℕ × List ℕ × ℕ)} (h : conjsK KR D = true) :
    ∀ e ∈ D, e.2.2 < KR.length ∧ conjK e.1 (KR.getD e.2.2 0) e.2.1 = true := by
  induction D with
  | nil => simp
  | cons e t ih =>
    change andB (andB (Nat.blt e.2.2 (lenK KR)) (conjK e.1 (getK KR e.2.2) e.2.1))
      (conjsK KR t) = true at h
    rw [andB_iff, andB_iff, Nat.blt_eq, lenK_eq, getK_eq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ih h.2 x hx

theorem certsK_sound {u : ℕ} {KR : List ℕ} {CD : List (List (List ℕ) × ℕ × ℕ)}
    (h : certsK u KR CD = true) :
    ∀ P ∈ KR, validK u P = true ∧ ∃ ws v w, certK u P ws v w = true := by
  induction KR generalizing CD with
  | nil => simp
  | cons P t ih =>
    cases CD with
    | nil =>
      change false = true at h
      exact absurd h (by decide)
    | cons c s =>
      change andB (andB (validK u P) (certK u P c.1 c.2.1 c.2.2)) (certsK u t s) = true at h
      rw [andB_iff, andB_iff] at h
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨h.1.1, c.1, c.2.1, c.2.2, h.1.2⟩
      · exact ih h.2 x hx

end CFSG.KC.Misc.Oq

end
