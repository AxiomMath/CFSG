module

public import Certificates.Data.Kernel.Misc.O73

public section

namespace CFSG.KS.PK

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O73

@[simp] theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

@[simp] theorem orB_eq (a b : Bool) : orB a b = (a || b) := by
  cases a <;> rfl

@[simp] theorem notB_eq (a : Bool) : notB a = !a := by
  cases a <;> rfl

@[simp] theorem impB_eq (a b : Bool) : impB a b = (!a || b) := by
  cases a <;> rfl

@[simp] theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

@[simp] theorem letN_eq (y : Nat) (k : Nat → Nat) : letN y k = k y := by
  cases y <;> rfl

@[simp] theorem letLN_eq (y : Nat) (k : Nat → List Nat) : letLN y k = k y := by
  cases y <;> rfl

private theorem allN_succ_eq (f : Nat → Bool) (m : Nat) :
    CFSG.KC.LQT.P.allN (m + 1) f = andB (f m) (CFSG.KC.LQT.P.allN m f) := rfl

theorem allN_lqt_iff {m : Nat} {f : Nat → Bool} :
    CFSG.KC.LQT.P.allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    rw [allN_succ_eq, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases (show i < m ∨ i = m by omega) with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h m (by omega), fun i hi => h i (by omega)⟩

private theorem allL_cons_eq (f : Nat → Bool) (x : Nat) (xs : List Nat) :
    CFSG.KC.LQT.P.allL (x :: xs) f = andB (f x) (CFSG.KC.LQT.P.allL xs f) := rfl

theorem allL_lqt_iff {l : List Nat} {f : Nat → Bool} :
    CFSG.KC.LQT.P.allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => by simp at hx, fun _ => rfl⟩
  | cons x xs ih =>
    rw [allL_cons_eq, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h1
      · exact h2 y hy'
    · intro h
      exact ⟨h x (by simp), fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

private theorem memN_rec_eq (x : Nat) (l : List Nat) :
    List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq x z) ih) l
      = decide (x ∈ l) := by
  induction l with
  | nil => rfl
  | cons z zs ih =>
    show orB (Nat.beq x z)
      (List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq x z) ih) zs)
      = decide (x ∈ z :: zs)
    rw [ih, orB_eq, Bool.eq_iff_iff]
    simp [Nat.beq_eq]

theorem memN_eq (x : Nat) (l : List Nat) : memN x l = decide (x ∈ l) := by
  show letB x (fun x => List.rec (motive := fun _ => Bool) false
    (fun z _ ih => orB (Nat.beq x z) ih) l) = decide (x ∈ l)
  rw [letB_eq]
  exact memN_rec_eq x l

private theorem lenN_cons_eq (x : Nat) (xs : List Nat) :
    CFSG.KC.Misc.lenN (x :: xs) = Nat.succ (CFSG.KC.Misc.lenN xs) := rfl

theorem lenN_misc_eq (l : List Nat) : CFSG.KC.Misc.lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [lenN_cons_eq, ih, List.length_cons]

theorem nodupN_eq (l : List Nat) : nodupN l = decide l.Nodup := by
  induction l with
  | nil => rfl
  | cons z t ih =>
    show andB (notB (memN z t)) (nodupN t) = decide (z :: t).Nodup
    rw [andB_eq, notB_eq, memN_eq, ih, Bool.eq_iff_iff]
    simp [List.nodup_cons]

private theorem allLL_cons_eq (f : List Nat → Bool) (x : List Nat) (xs : List (List Nat)) :
    allLL (x :: xs) f = andB (f x) (allLL xs f) := rfl

theorem allLL_iff {L : List (List Nat)} {f : List Nat → Bool} :
    allLL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => by simp at hx, fun _ => rfl⟩
  | cons x xs ih =>
    rw [allLL_cons_eq, andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact h1
      · exact h2 y hy'
    · intro h
      exact ⟨h x (by simp), fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

private theorem anyLL_cons_eq (f : List Nat → Bool) (x : List Nat) (xs : List (List Nat)) :
    anyLL (x :: xs) f = orB (f x) (anyLL xs f) := rfl

theorem anyLL_iff {L : List (List Nat)} {f : List Nat → Bool} :
    anyLL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => show false = true ↔ _; simp
  | cons x xs ih =>
    rw [anyLL_cons_eq, orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact ⟨x, by simp, h⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, h⟩
    · rintro ⟨y, hy, h⟩
      rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inl h
      · exact Or.inr ⟨y, hy', h⟩

theorem eqLN_eq (a b : List Nat) : eqLN a b = decide (a = b) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y t => rfl
  | cons x a' ih =>
    cases b with
    | nil => rfl
    | cons y t =>
      show andB (Nat.beq x y) (eqLN a' t) = decide (x :: a' = y :: t)
      rw [andB_eq, ih t, Bool.eq_iff_iff]
      simp [Nat.beq_eq]

theorem nthN_eq (l : List Nat) (i : Nat) : wordM7.nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show wordM7.nthN xs j = (x :: xs).getD (j + 1) 0
      rw [List.getD_cons_succ, ih j]

theorem nthL_eq (L : List (List Nat)) (i : Nat) : nthL L i = L.getD i [] := by
  induction L generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ j =>
      show nthL xs j = (x :: xs).getD (j + 1) []
      rw [List.getD_cons_succ, ih j]

theorem lenLLN_eq (L : List (List Nat)) : relPK.lenLLN L = L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    show Nat.succ (relPK.lenLLN xs) = xs.length + 1
    rw [ih]

end CFSG.KS.PK

end
