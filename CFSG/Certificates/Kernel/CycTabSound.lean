module

public import Certificates.Data.Kernel.CycTab
public import Mathlib.GroupTheory.Perm.List

public section

namespace CFSG.KC.CycTab

open Equiv

@[expose] def codeOf {k : Nat} (l : Fin k × Bool) : Nat := 2 * l.1.val + cond l.2 0 1

@[expose] def letter {n k : Nat} (G : Fin k → Perm (Fin n)) (l : Fin k × Bool) : Perm (Fin n) :=
  cond l.2 (G l.1) (G l.1)⁻¹

@[expose] def LetterOK {n k : Nat} (TT : Nat) (G : Fin k → Perm (Fin n)) : Prop :=
  ∀ (l : Fin k × Bool) (x : Fin n), (letter G l x).val = fgK TT (codeOf l * n + x.val)

@[expose] def cycsPerm (n : Nat) [NeZero n] (cs : List (List Nat)) : Perm (Fin n) :=
  (cs.map fun c => (c.map (Fin.ofNat n)).formPerm).prod

theorem brec_and (c y : Bool) :
    Bool.rec (motive := fun _ => Bool) false y c = true ↔ c = true ∧ y = true := by
  cases c <;> simp

theorem allLtK_iff (p : Nat → Bool) : ∀ n, allLtK n p = true ↔ ∀ i < n, p i = true
  | 0 => by simp [allLtK]
  | k + 1 => by
    change Bool.rec (motive := fun _ => Bool) false (allLtK k p) (p k) = true ↔ _
    rw [brec_and, allLtK_iff p k]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact h1
    · intro H
      exact ⟨H k (by omega), fun i hi => H i (by omega)⟩

theorem swapK_eq (a b x : Nat) : swapK a b x = if x = a then b else if x = b then a else x := by
  unfold swapK
  split_ifs with h1 h2
  · rw [h1, Nat.beq_refl]
  · have e1 : Nat.beq x a = false := by
      cases h : Nat.beq x a
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h1
    rw [e1, h2, Nat.beq_refl]
  · have e1 : Nat.beq x a = false := by
      cases h : Nat.beq x a
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h1
    have e2 : Nat.beq x b = false := by
      cases h : Nat.beq x b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h2
    rw [e1, e2]

variable {n : Nat} [NeZero n]

theorem swap_val (a b : Nat) (y : Fin n) :
    (swap (Fin.ofNat n a) (Fin.ofNat n b) y).val = swapK (a % n) (b % n) y.val := by
  rw [swapK_eq, swap_apply_def]
  split_ifs <;> simp_all [Fin.ext_iff]

theorem cycGoK_spec (x : Fin n) : ∀ (l : List Nat) (a : Nat),
    (((a :: l).map (Fin.ofNat n)).formPerm x).val = cycGoK n x.val a l
  | [], a => by simp [cycGoK]
  | b :: l, a => by
    rw [List.map_cons, List.map_cons, List.formPerm_cons_cons, Perm.mul_apply]
    have ih := cycGoK_spec x l b
    rw [List.map_cons] at ih
    change _ = swapK (a % n) (b % n) (cycGoK n x.val b l)
    rw [← ih, swap_val]

theorem cycK_spec (x : Fin n) (c : List Nat) :
    ((c.map (Fin.ofNat n)).formPerm x).val = cycK n c x.val := by
  cases c with
  | nil => simp [cycK]
  | cons a l => exact cycGoK_spec x l a

theorem cycsK_spec (x : Fin n) : ∀ cs : List (List Nat), (cycsPerm n cs x).val = cycsK n cs x.val
  | [] => by simp [cycsPerm, cycsK]
  | c :: cs => by
    rw [cycsPerm, List.map_cons, List.prod_cons, Perm.mul_apply, cycK_spec]
    change cycK n c (cycsPerm n cs x).val = cycK n c (cycsK n cs x.val)
    rw [cycsK_spec x cs]

theorem genOK_spec {cs : List (List Nat)} {TT i : Nat} (h : genOK n cs TT i = true) (x : Fin n) :
    (cycsPerm n cs x).val = fgK TT (2 * i * n + x.val) ∧
    ((cycsPerm n cs)⁻¹ x).val = fgK TT ((2 * i + 1) * n + x.val) := by
  have H := (allLtK_iff _ n).1 h
  have hp : ∀ y : Fin n, fgK TT (2 * i * n + y.val) = cycsK n cs y.val ∧
      fgK TT ((2 * i + 1) * n + y.val) < n ∧
      fgK TT (2 * i * n + fgK TT ((2 * i + 1) * n + y.val)) = y.val := by
    intro y
    have := H y.val y.isLt
    rw [brec_and, brec_and] at this
    simp only [Nat.beq_eq, Nat.blt_eq] at this
    exact ⟨this.1, this.2.1, this.2.2⟩
  refine ⟨?_, ?_⟩
  · rw [cycsK_spec, (hp x).1]
  · obtain ⟨-, hlt, hfix⟩ := hp x
    have hy : cycsPerm n cs ⟨_, hlt⟩ = x := by
      apply Fin.ext
      rw [cycsK_spec, ← (hp ⟨_, hlt⟩).1]
      exact hfix
    rw [Perm.inv_eq_iff_eq.2 hy.symm]

omit [NeZero n] in
theorem gensGoK_spec {CS : List (List (List Nat))} {TT : Nat} :
    ∀ {i : Nat}, gensGoK n CS TT i = true → ∀ j < CS.length, genOK n (CS.getD j []) TT (i + j) = true := by
  induction CS with
  | nil => intro i _ j hj; simp at hj
  | cons cs CS ih =>
    intro i h j hj
    change Bool.rec (motive := fun _ => Bool) false (gensGoK n CS TT (Nat.succ i))
      (genOK n cs TT i) = true at h
    rw [brec_and] at h
    cases j with
    | zero =>
      rw [List.getD_cons_zero, Nat.add_zero]
      exact h.1
    | succ j =>
      have := ih h.2 j (by simp at hj; omega)
      rw [List.getD_cons_succ, show i + (j + 1) = Nat.succ i + j by omega]
      exact this

theorem gens_sound {k : Nat} {CS : List (List (List Nat))} {TT : Nat} {G : Fin k → Perm (Fin n)}
    (hk : k ≤ CS.length) (hG : ∀ i : Fin k, G i = cycsPerm n (CS.getD i.val []))
    (h : gensOK n CS TT = true) : LetterOK TT G := by
  rintro ⟨i, b⟩ x
  have hi := gensGoK_spec h i.val (by omega)
  rw [Nat.zero_add] at hi
  have := genOK_spec hi x
  cases b
  · simp only [letter, Bool.cond_false, codeOf, hG]
    exact this.2
  · simp only [letter, Bool.cond_true, codeOf, Nat.add_zero, hG]
    exact this.1

omit [NeZero n] in
theorem word_val {k : Nat} {TT : Nat} {G : Fin k → Perm (Fin n)} (hL : LetterOK TT G) (x : Fin n) :
    ∀ w : List (Fin k × Bool),
      ((w.map (letter G)).prod x).val = wordK n TT (w.map codeOf) x.val
  | [] => by simp [wordK]
  | l :: w => by
    rw [List.map_cons, List.prod_cons, Perm.mul_apply, hL, word_val hL x w]
    rfl

omit [NeZero n] in
theorem relsOK_spec {TT : Nat} : ∀ {RS : List (List Nat)}, relsOK n TT RS = true →
    ∀ v ∈ RS, ∀ x < n, wordK n TT v (wordK n TT v x) = x
  | [], _ => by simp
  | v :: RS, h => by
    change Bool.rec (motive := fun _ => Bool) false (relsOK n TT RS) (sqOK n TT v) = true at h
    rw [brec_and] at h
    intro u hu x hx
    rcases List.mem_cons.1 hu with rfl | hu
    · have := (allLtK_iff _ n).1 h.1 x hx
      simpa using this
    · exact relsOK_spec h.2 u hu x hx

omit [NeZero n] in
theorem sq_sound {k : Nat} {TT : Nat} {G : Fin k → Perm (Fin n)} {RS : List (List Nat)}
    (hL : LetterOK TT G) (h : relsOK n TT RS = true) (w : List (Fin k × Bool))
    (hw : w.map codeOf ∈ RS) : (w.map (letter G)).prod * (w.map (letter G)).prod = 1 := by
  ext x
  rw [Perm.mul_apply, word_val hL, word_val hL]
  exact relsOK_spec h _ hw x.val x.isLt

end CFSG.KC.CycTab

end
