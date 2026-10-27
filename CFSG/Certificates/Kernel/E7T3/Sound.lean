module

public import Certificates.Data.Kernel.E7T3.Defs

public section

namespace CFSG.KC.E7T3

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley CFSG.Blueprint

theorem bandK_eq (a b : Bool) : bandK a b = (a && b) := by cases a <;> rfl

theorem beqB_eq_true {a b : Bool} (h : beqB a b = true) : (a = true ↔ b = true) := by
  cases a <;> cases b <;> simp_all [beqB]

theorem brec_eq {α : Sort _} (f t : α) (b : Bool) :
    (Bool.rec f t b : α) = if b = true then t else f := by
  cases b <;> rfl

theorem allL_iff {α : Type} (p : α → Bool) (l : List α) :
    allL p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [allL]
  | cons a l ih =>
    change bandK (p a) (allL p l) = true ↔ _
    rw [bandK_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyL_iff {α : Type} (p : α → Bool) (l : List α) :
    anyL p l = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil => simp [anyL]
  | cons a l ih =>
    change (Bool.rec (anyL p l) true (p a) : Bool) = true ↔ _
    rw [brec_eq]
    by_cases h : p a = true
    · rw [if_pos h]
      exact ⟨fun _ => ⟨a, List.mem_cons_self, h⟩, fun _ => rfl⟩
    · rw [if_neg h, ih]
      constructor
      · rintro ⟨x, hx, hp⟩
        exact ⟨x, List.mem_cons_of_mem _ hx, hp⟩
      · rintro ⟨x, hx, hp⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact absurd hp h
        · exact ⟨x, hx, hp⟩

theorem allNK_iff (n : ℕ) (f : ℕ → Bool) : allNK n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => simp [allNK]
  | succ n ih =>
    change bandK (f n) (allNK n f) = true ↔ _
    rw [bandK_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h2 k hk
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem memK_iff (x : ℕ) (l : List ℕ) : memK x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memK]
  | cons a l ih =>
    change (Bool.rec (memK x l) true (Nat.beq x a) : Bool) = true ↔ _
    rw [brec_eq, List.mem_cons, ← ih]
    by_cases h : x = a
    · rw [if_pos (by rw [h]; exact Nat.beq_refl a)]
      exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
    · rw [if_neg (fun e => h (Nat.eq_of_beq_eq_true e))]
      exact ⟨Or.inr, fun e => e.resolve_left h⟩

theorem memLoK_iff (e : ℕ) (l : List ℕ) : memLoK e l = true ↔ ∃ q ∈ l, e = loK q := by
  induction l with
  | nil => simp [memLoK]
  | cons a l ih =>
    change (Bool.rec (memLoK e l) true (Nat.beq e (loK a)) : Bool) = true ↔ _
    rw [brec_eq]
    by_cases h : e = loK a
    · rw [if_pos (by rw [h]; exact Nat.beq_refl _)]
      exact ⟨fun _ => ⟨a, List.mem_cons_self, h⟩, fun _ => rfl⟩
    · rw [if_neg (fun e' => h (Nat.eq_of_beq_eq_true e')), ih]
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨q, List.mem_cons_of_mem _ hq, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact absurd rfl h
        · exact ⟨q, hq, rfl⟩

theorem listEqK_eq : ∀ (a b : List ℕ), listEqK a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h => absurd (h : false = true) Bool.false_ne_true
  | x :: a, y :: b, h => by
    change bandK (Nat.beq x y) (listEqK a b) = true at h
    rw [bandK_eq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, listEqK_eq a b h.2]

theorem lnK_eq (x s : ℕ) : lnK x s = x / 2 ^ s % 256 := by
  unfold lnK
  change (x >>> s) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem BAD_eq : BAD = 2 ^ 56 := rfl

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

theorem ofFn_seven {α : Type} (f : Fin Tag.E7.rank → α) :
    List.ofFn f = [f (0 : Fin 7), f (1 : Fin 7), f (2 : Fin 7), f (3 : Fin 7), f (4 : Fin 7),
      f (5 : Fin 7), f (6 : Fin 7)] :=
  rfl

def pk (a0 a1 a2 a3 a4 a5 a6 : ℕ) : ℕ :=
  a0 + 256 * a1 + 65536 * a2 + 16777216 * a3 + 4294967296 * a4 + 1099511627776 * a5 +
    281474976710656 * a6

theorem exists_pk {x : ℕ} (hx : x < BAD) : ∃ a0 a1 a2 a3 a4 a5 a6 : ℕ, a0 < 256 ∧ a1 < 256 ∧
    a2 < 256 ∧ a3 < 256 ∧ a4 < 256 ∧ a5 < 256 ∧ a6 < 256 ∧ x = pk a0 a1 a2 a3 a4 a5 a6 := by
  rw [BAD_eq] at hx
  refine ⟨x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256, x / 4294967296 % 256,
    x / 1099511627776 % 256, x / 281474976710656 % 256, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_⟩
  unfold pk
  omega

section Lanes

variable {a0 a1 a2 a3 a4 a5 a6 : ℕ} (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256)
  (h3 : a3 < 256) (h4 : a4 < 256) (h5 : a5 < 256) (h6 : a6 < 256)
include h0 h1 h2 h3 h4 h5 h6

theorem pk_lt : pk a0 a1 a2 a3 a4 a5 a6 < BAD := by
  rw [BAD_eq]
  unfold pk
  omega

theorem lnK_pk : lnK (pk a0 a1 a2 a3 a4 a5 a6) 0 = a0 ∧ lnK (pk a0 a1 a2 a3 a4 a5 a6) 8 = a1 ∧
    lnK (pk a0 a1 a2 a3 a4 a5 a6) 16 = a2 ∧ lnK (pk a0 a1 a2 a3 a4 a5 a6) 24 = a3 ∧
    lnK (pk a0 a1 a2 a3 a4 a5 a6) 32 = a4 ∧ lnK (pk a0 a1 a2 a3 a4 a5 a6) 40 = a5 ∧
    lnK (pk a0 a1 a2 a3 a4 a5 a6) 48 = a6 := by
  simp only [lnK_eq, pk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem toV_pk : toV (pk a0 a1 a2 a3 a4 a5 a6) =
    fun j : Fin 7 => ((![a0, a1, a2, a3, a4, a5, a6] j : ℕ) : ℤ) - 128 := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  funext j
  fin_cases j <;> simp [toV, l0, l1, l2, l3, l4, l5, l6] <;> rfl

theorem decL_pk : decL (pk a0 a1 a2 a3 a4 a5 a6) =
    [(a0 : ℤ) - 128, (a1 : ℤ) - 128, (a2 : ℤ) - 128, (a3 : ℤ) - 128, (a4 : ℤ) - 128,
      (a5 : ℤ) - 128, (a6 : ℤ) - 128] := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [decL, vofFn, ofFn_seven]
  simp [toV, l0, l1, l2, l3, l4, l5, l6]

end Lanes

theorem setK_spec {x s old c plus : ℕ} (h : setK x s old c plus < BAD) :
    x < BAD ∧ old + c ≤ plus ∧ plus - (old + c) < 256 ∧
      setK x s old c plus = x - old * 2 ^ s + (plus - (old + c)) * 2 ^ s := by
  unfold setK at h ⊢
  simp only [brec_eq, Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.sub_eq] at h ⊢
  by_cases h1 : x < BAD
  · by_cases h2 : old + c ≤ plus
    · by_cases h3 : plus - (old + c) < 256
      · simp only [h1, h2, h3, if_true]
        refine ⟨trivial, trivial, trivial, ?_⟩
        simp only [updK, Nat.add_eq, Nat.sub_eq, shl_eq]
      · simp [h1, h2, h3] at h
    · simp [h1, h2] at h
  · simp [h1] at h

theorem cartanE7_apply : ∀ i j : Fin 7, Tag.E7.cartan i j =
    ![![2, 0, -1, 0, 0, 0, 0], ![0, 2, 0, -1, 0, 0, 0], ![-1, 0, 2, -1, 0, 0, 0],
      ![0, -1, -1, 2, -1, 0, 0], ![0, 0, 0, -1, 2, -1, 0], ![0, 0, 0, 0, -1, 2, -1],
      ![0, 0, 0, 0, 0, -1, 2]] i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem reflect_apply (i j : Fin 7) (v : Fin Tag.E7.rank → ℤ) :
    reflect Tag.E7 i v j = v j - (v (0 : Fin 7) * Tag.E7.cartan i (0 : Fin 7) +
      v (1 : Fin 7) * Tag.E7.cartan i (1 : Fin 7) + v (2 : Fin 7) * Tag.E7.cartan i (2 : Fin 7) +
      v (3 : Fin 7) * Tag.E7.cartan i (3 : Fin 7) + v (4 : Fin 7) * Tag.E7.cartan i (4 : Fin 7) +
      v (5 : Fin 7) * Tag.E7.cartan i (5 : Fin 7) + v (6 : Fin 7) * Tag.E7.cartan i (6 : Fin 7)) *
        (Pi.single i (1 : ℤ) : Fin 7 → ℤ) j := by
  change v j - (∑ m : Fin 7, Tag.E7.cartan i m * v m) * ((Pi.single i (1 : ℤ) : Fin 7 → ℤ) j) = _
  rw [Fin.sum_univ_seven]
  ring

theorem stepK_0 (x : ℕ) : stepK 0 x = setK x 0 (lnK x 0) 0 (Nat.add (lnK x 16) 128) := rfl
theorem stepK_1 (x : ℕ) : stepK 1 x = setK x 8 (lnK x 8) 0 (Nat.add (lnK x 24) 128) := rfl
theorem stepK_2 (x : ℕ) : stepK 2 x = setK x 16 (lnK x 16) 0 (Nat.add (lnK x 0) (lnK x 24)) := rfl
theorem stepK_3 (x : ℕ) : stepK 3 x =
    setK x 24 (lnK x 24) 128 (Nat.add (Nat.add (lnK x 8) (lnK x 16)) (lnK x 32)) := rfl
theorem stepK_4 (x : ℕ) : stepK 4 x =
    setK x 32 (lnK x 32) 0 (Nat.add (lnK x 24) (lnK x 40)) := rfl
theorem stepK_5 (x : ℕ) : stepK 5 x =
    setK x 40 (lnK x 40) 0 (Nat.add (lnK x 32) (lnK x 48)) := rfl
theorem stepK_6 (x : ℕ) : stepK 6 x = setK x 48 (lnK x 48) 0 (Nat.add (lnK x 40) 128) := rfl

theorem spec0 (x : ℕ) (h : stepK 0 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 0 x) j = reflect Tag.E7 (0 : Fin 7) (toV x) j := by
  rw [stepK_0] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨l0, -, l2, -, -, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l0, l2] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a0 * 2 ^ 0 + (Nat.add a2 128 - (a0 + 0)) * 2 ^ 0 =
      pk (a2 + 128 - a0) a1 a2 a3 a4 a5 a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk (by omega) h1 h2 h3 h4 h5 h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem spec1 (x : ℕ) (h : stepK 1 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 1 x) j = reflect Tag.E7 (1 : Fin 7) (toV x) j := by
  rw [stepK_1] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, l1, -, l3, -, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l1, l3] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a1 * 2 ^ 8 + (Nat.add a3 128 - (a1 + 0)) * 2 ^ 8 =
      pk a0 (a3 + 128 - a1) a2 a3 a4 a5 a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 (by omega) h2 h3 h4 h5 h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem spec2 (x : ℕ) (h : stepK 2 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 2 x) j = reflect Tag.E7 (2 : Fin 7) (toV x) j := by
  rw [stepK_2] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨l0, -, l2, l3, -, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l0, l2, l3] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a2 * 2 ^ 16 + (Nat.add a0 a3 - (a2 + 0)) * 2 ^ 16 =
      pk a0 a1 (a0 + a3 - a2) a3 a4 a5 a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 h1 (by omega) h3 h4 h5 h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

set_option maxRecDepth 8000 in
theorem spec3 (x : ℕ) (h : stepK 3 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 3 x) j = reflect Tag.E7 (3 : Fin 7) (toV x) j := by
  rw [stepK_3] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, l1, l2, l3, l4, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l1, l2, l3, l4] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a3 * 2 ^ 24 +
      (Nat.add (Nat.add a1 a2) a4 - (a3 + 128)) * 2 ^ 24 =
      pk a0 a1 a2 (a1 + a2 + a4 - (a3 + 128)) a4 a5 a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 h1 h2 (by omega) h4 h5 h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem spec4 (x : ℕ) (h : stepK 4 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 4 x) j = reflect Tag.E7 (4 : Fin 7) (toV x) j := by
  rw [stepK_4] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, -, -, l3, l4, l5, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l3, l4, l5] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a4 * 2 ^ 32 + (Nat.add a3 a5 - (a4 + 0)) * 2 ^ 32 =
      pk a0 a1 a2 a3 (a3 + a5 - a4) a5 a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 h1 h2 h3 (by omega) h5 h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem spec5 (x : ℕ) (h : stepK 5 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 5 x) j = reflect Tag.E7 (5 : Fin 7) (toV x) j := by
  rw [stepK_5] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, -, -, -, l4, l5, l6⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l4, l5, l6] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a5 * 2 ^ 40 + (Nat.add a4 a6 - (a5 + 0)) * 2 ^ 40 =
      pk a0 a1 a2 a3 a4 (a4 + a6 - a5) a6 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 h1 h2 h3 h4 (by omega) h6]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem spec6 (x : ℕ) (h : stepK 6 x < BAD) :
    x < BAD ∧ ∀ j : Fin 7, toV (stepK 6 x) j = reflect Tag.E7 (6 : Fin 7) (toV x) j := by
  rw [stepK_6] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, -, -, -, -, l5, l6⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  rw [l5, l6] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5 h6, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 a6 - a6 * 2 ^ 48 + (Nat.add a5 128 - (a6 + 0)) * 2 ^ 48 =
      pk a0 a1 a2 a3 a4 a5 (a5 + 128 - a6) := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk h0 h1 h2 h3 h4 h5 (by omega)]
  fin_cases j <;> simp [cartanE7_apply] <;> omega

theorem stepK_spec (i : Fin Tag.E7.rank) (x : ℕ) (h : stepK i.val x < BAD) :
    x < BAD ∧ toV (stepK i.val x) = reflect Tag.E7 i (toV x) := by
  fin_cases i
  · obtain ⟨a, b⟩ := spec0 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec1 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec2 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec3 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec4 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec5 x h
    exact ⟨a, funext b⟩
  · obtain ⟨a, b⟩ := spec6 x h
    exact ⟨a, funext b⟩

theorem actK_spec (w : List (Fin Tag.E7.rank)) (x : ℕ) (h : actK w x < BAD) :
    x < BAD ∧ toV (actK w x) = (wordMat Tag.E7 w).mulVec (toV x) := by
  induction w with
  | nil => exact ⟨h, by rw [wordMat_nil, Matrix.one_mulVec]; rfl⟩
  | cons i w ih =>
    change stepK i.val (actK w x) < BAD at h
    obtain ⟨h1, h2⟩ := stepK_spec i _ h
    obtain ⟨h3, h4⟩ := ih h1
    refine ⟨h3, ?_⟩
    change toV (stepK i.val (actK w x)) = _
    rw [h2, h4, wordMat_cons, ← Matrix.mulVec_mulVec, reflMat_mulVec]

theorem actRevK_spec (w : List (Fin Tag.E7.rank)) :
    ∀ x : ℕ, actRevK w x < BAD →
      x < BAD ∧ toV (actRevK w x) = (wordMat Tag.E7 w.reverse).mulVec (toV x) := by
  induction w with
  | nil => intro x h; exact ⟨h, by rw [List.reverse_nil, wordMat_nil, Matrix.one_mulVec]; rfl⟩
  | cons i w ih =>
    intro x h
    change actRevK w (stepK i.val x) < BAD at h
    obtain ⟨h1, h2⟩ := ih _ h
    obtain ⟨h3, h4⟩ := stepK_spec i x h1
    refine ⟨h3, ?_⟩
    change toV (actRevK w (stepK i.val x)) = _
    rw [h2, h4, List.reverse_cons, wordMat_append, wordMat_cons, wordMat_nil, mul_one,
      ← Matrix.mulVec_mulVec, reflMat_mulVec]

theorem lmulVec_eq_vofFn (n : ℕ) (A : List (List ℤ)) (v : List ℤ) :
    lmulVec n A v = vofFn n (toVec n (lmulVec n A v)) := by
  unfold lmulVec
  rw [toVec_vofFn]

theorem lmulVec_decL_mat (w : List (Fin Tag.E7.rank)) (x : ℕ) :
    lmulVec Tag.E7.rank (e7wl w) (decL x) =
      vofFn Tag.E7.rank ((wordMat Tag.E7 w).mulVec (toV x)) := by
  rw [lmulVec_eq_vofFn, toVec_lmulVec, ← wordMat_e7wl, decL, toVec_vofFn]

theorem lmulVec_decL (w : List (Fin Tag.E7.rank)) (x : ℕ) (h : actK w x < BAD) :
    lmulVec Tag.E7.rank (e7wl w) (decL x) = decL (actK w x) := by
  rw [lmulVec_decL_mat, decL, (actK_spec w x h).2]

theorem decL_inj {x y : ℕ} (hx : x < BAD) (hy : y < BAD) (h : decL x = decL y) : x = y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk hx
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, g0, g1, g2, g3, g4, g5, g6, rfl⟩ := exists_pk hy
  have h' := List.ofFn_injective h
  rw [toV_pk h0 h1 h2 h3 h4 h5 h6, toV_pk g0 g1 g2 g3 g4 g5 g6] at h'
  have e0 := congrFun h' 0
  have e1 := congrFun h' 1
  have e2 := congrFun h' 2
  have e3 := congrFun h' 3
  have e4 := congrFun h' 4
  have e5 := congrFun h' 5
  have e6 := congrFun h' 6
  simp at e0 e1 e2 e3 e4 e5 e6
  unfold pk
  omega

theorem perm3K_spec (x : ℕ) (hx : x < BAD) :
    (perm3K x 8 48 32 < BAD ∧ decL (perm3K x 8 48 32) = e7perm3 1 6 4 (decL x)) ∧
    (perm3K x 8 32 48 < BAD ∧ decL (perm3K x 8 32 48) = e7perm3 1 4 6 (decL x)) ∧
    (perm3K x 8 32 16 < BAD ∧ decL (perm3K x 8 32 16) = e7perm3 1 4 2 (decL x)) ∧
    (perm3K x 8 16 32 < BAD ∧ decL (perm3K x 8 16 32) = e7perm3 1 2 4 (decL x)) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := exists_pk hx
  obtain ⟨-, l1, l2, -, l4, -, l6⟩ := lnK_pk h0 h1 h2 h3 h4 h5 h6
  have e1 : perm3K (pk a0 a1 a2 a3 a4 a5 a6) 8 48 32 = pk a0 a4 a2 a3 a6 a5 a1 := by
    simp only [perm3K, updK, l1, l4, l6]
    simp only [Nat.add_eq, Nat.sub_eq, shl_eq, Nat.reducePow]
    unfold pk
    omega
  have e2 : perm3K (pk a0 a1 a2 a3 a4 a5 a6) 8 32 48 = pk a0 a6 a2 a3 a1 a5 a4 := by
    simp only [perm3K, updK, l1, l4, l6]
    simp only [Nat.add_eq, Nat.sub_eq, shl_eq, Nat.reducePow]
    unfold pk
    omega
  have e3 : perm3K (pk a0 a1 a2 a3 a4 a5 a6) 8 32 16 = pk a0 a2 a4 a3 a1 a5 a6 := by
    simp only [perm3K, updK, l1, l2, l4]
    simp only [Nat.add_eq, Nat.sub_eq, shl_eq, Nat.reducePow]
    unfold pk
    omega
  have e4 : perm3K (pk a0 a1 a2 a3 a4 a5 a6) 8 16 32 = pk a0 a4 a1 a3 a2 a5 a6 := by
    simp only [perm3K, updK, l1, l2, l4]
    simp only [Nat.add_eq, Nat.sub_eq, shl_eq, Nat.reducePow]
    unfold pk
    omega
  rw [e1, e2, e3, e4]
  refine ⟨⟨pk_lt h0 h4 h2 h3 h6 h5 h1, ?_⟩, ⟨pk_lt h0 h6 h2 h3 h1 h5 h4, ?_⟩,
    ⟨pk_lt h0 h2 h4 h3 h1 h5 h6, ?_⟩, ⟨pk_lt h0 h4 h1 h3 h2 h5 h6, ?_⟩⟩ <;>
  all_goals
    rw [decL_pk h0 h1 h2 h3 h4 h5 h6]
    first
      | rw [decL_pk h0 h4 h2 h3 h6 h5 h1]
      | rw [decL_pk h0 h6 h2 h3 h1 h5 h4]
      | rw [decL_pk h0 h2 h4 h3 h1 h5 h6]
      | rw [decL_pk h0 h4 h1 h3 h2 h5 h6]
    simp [e7perm3, ofFn_seven, vget]

theorem permK_spec (k : ℕ) (rot : Bool) (x : ℕ) (hx : x < BAD) :
    permK k rot x < BAD ∧ decL (permK k rot x) = e7T3Perm k rot (decL x) := by
  obtain ⟨p1, p2, p3, p4⟩ := perm3K_spec x hx
  unfold permK e7T3Perm
  simp only [brec_eq, Nat.beq_eq]
  by_cases h1 : k = 1
  · cases rot <;> simp [h1, p1, p2]
  · by_cases h2 : k = 2
    · cases rot <;> simp [h1, h2, p3, p4]
    · simp [h1, h2, hx]

structure DataOK (s0 s1 s2 s3 roots : List ℕ) : Prop where
  std : ∀ k, (stdSel s0 s1 s2 s3 k).map decL = e7StdRoots (e7T3Nodes k)
  stdv : ∀ k, ∀ p ∈ stdSel s0 s1 s2 s3 k, p < BAD
  rts : roots.map (fun q => decL (loK q)) = Tag.E7.artifactRoots
  rk : rootsK roots = true

theorem dataOK_of {s0 s1 s2 s3 roots : List ℕ}
    (h0 : s0.map decL = e7StdRoots (e7T3Nodes 0)) (h1 : s1.map decL = e7StdRoots (e7T3Nodes 1))
    (h2 : s2.map decL = e7StdRoots (e7T3Nodes 2)) (h3 : s3.map decL = e7StdRoots (e7T3Nodes 3))
    (v0 : validK s0 = true) (v1 : validK s1 = true) (v2 : validK s2 = true)
    (v3 : validK s3 = true) (hr : roots.map (fun q => decL (loK q)) = Tag.E7.artifactRoots)
    (hk : rootsK roots = true) : DataOK s0 s1 s2 s3 roots where
  std k := by
    rcases k with _ | _ | _ | k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  stdv k := by
    unfold validK at v0 v1 v2 v3
    rw [allL_iff] at v0 v1 v2 v3
    simp only [Nat.blt_eq] at v0 v1 v2 v3
    rcases k with _ | _ | _ | k
    · exact v0
    · exact v1
    · exact v2
    · exact v3
  rts := hr
  rk := hk

theorem classOK_spec {cl : ℕ} {ρ : ERow} (h : classOK cl ρ = true) :
    cl < 21 ∧ ∀ i < 21, ((∃ u ∈ eUnits, ρ = escale u (e7T3G i)) ↔ i = cl) := by
  unfold classOK at h
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq, allNK_iff] at h
  refine ⟨h.1, fun i hi => ?_⟩
  have := beqB_eq_true (h.2 i hi)
  rw [decide_eq_true_iff, Nat.beq_eq] at this
  exact this

theorem rootsK_spec {roots : List ℕ} (h : rootsK roots = true) {q : ℕ} (hq : q ∈ roots) :
    loK q < BAD ∧ hiK q < 21 ∧ ∀ i < 21, (RowIs (decL (loK q)) i ↔ i = hiK q) := by
  unfold rootsK at h
  have h' := (allL_iff _ _).1 h q hq
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq] at h'
  obtain ⟨h1, h2⟩ := classOK_spec h'.2
  exact ⟨h'.1, h1, h2⟩

theorem compK_spec {S : List ℕ} {k : ℕ} (hS : S.map decL = e7StdRoots (e7T3Nodes k))
    (hv : ∀ p ∈ S, p < BAD) {w : List (Fin Tag.E7.rank)} {cm : E7T3Comp} (hk : cm.kind = k)
    (h : compK S w cm = true) : cm.Good e7T3Word w := by
  unfold compK at h
  rw [bandK_eq, Bool.and_eq_true, decide_eq_true_iff, allL_iff] at h
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  intro l hl
  rw [hk, ← hS] at hl
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
  have h5 := h4 p hp
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h5
  obtain ⟨hlt, heq⟩ := h5
  obtain ⟨hA, eA⟩ := actRevK_spec w _ hlt
  obtain ⟨hB, eB⟩ := actK_spec e7T3Word _ hA
  obtain ⟨-, eC⟩ := actK_spec w p hB
  rw [heq] at hlt
  obtain ⟨hD, eD⟩ := actK_spec cm.u _ hlt
  obtain ⟨-, eP⟩ := permK_spec cm.kind cm.rot p (hv p hp)
  rw [← eP, lmulVec_decL_mat, lmulVec_decL_mat, ← eD, ← heq, eA, eB, eC, wordMat_append,
    wordMat_append, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem good_of_goodK {s0 s1 s2 s3 roots : List ℕ} (hD : DataOK s0 s1 s2 s3 roots)
    {c : E7T3Cert} {R : List ℕ} (h : goodK s0 s1 s2 s3 roots c R = true) : c.Good := by
  unfold goodK at h
  simp only [bandK_eq, Bool.and_eq_true, decide_eq_true_iff, allL_iff] at h
  obtain ⟨hcls, hcomp, hrl, hin, hiff⟩ := h
  have hR := (listEqK_eq _ _ hrl).symm
  have hRv : ∀ e ∈ R, ∃ q ∈ roots, e = loK q ∧ loK q < BAD := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := (memLoK_iff _ _).1 (hin e he)
    exact ⟨q, hq, rfl, (rootsK_spec hD.rk hq).1⟩
  have hRL : c.rootList = R.map decL := by
    rw [hR, rlK, List.map_flatMap, E7T3Cert.rootList]
    refine flatMap_congr' fun cm hcm => ?_
    rw [← hD.std cm.kind, List.map_map, List.map_map]
    refine List.map_congr_left fun p hp => ?_
    have hmem : actK c.w p ∈ R := by
      rw [hR, rlK, List.mem_flatMap]
      exact ⟨cm, hcm, List.mem_map_of_mem hp⟩
    obtain ⟨q, -, he, hlt⟩ := hRv _ hmem
    rw [← he] at hlt
    exact lmulVec_decL c.w p hlt
  refine ⟨fun cm hcm => compK_spec (hD.std cm.kind) (hD.stdv cm.kind) rfl (hcomp cm hcm),
    hcls, ?_, ?_⟩
  · intro r hr
    rw [hRL] at hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
    obtain ⟨q, hq, rfl, -⟩ := hRv e he
    rw [← hD.rts]
    exact List.mem_map_of_mem hq
  · intro r hr
    rw [← hD.rts] at hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
    obtain ⟨hlt, hcl, hrow⟩ := rootsK_spec hD.rk hq
    have hi := beqB_eq_true (hiff q hq)
    rw [memK_iff, memK_iff] at hi
    rw [hRL]
    constructor
    · rintro ⟨i, hi', hrw⟩
      have := (hrow i (hcls i hi')).1 hrw
      subst this
      exact List.mem_map_of_mem (hi.1 hi')
    · intro hm
      obtain ⟨e, he, hde⟩ := List.mem_map.1 hm
      obtain ⟨q', -, rfl, hlt'⟩ := hRv e he
      have := decL_inj hlt' hlt hde
      rw [this] at he
      exact ⟨hiK q, hi.2 he, (hrow _ hcl).2 rfl⟩

theorem flats_of_flatsK (h : flatsK = true) : ∀ i j : Fin 21, i < j → ∃ c ∈ e7T3Certs,
    ∀ l : Fin 21, (edet3 (e7T3G i) (e7T3G j) (e7T3G l) = (0, 0) ↔ l.val ∈ c.cls) := by
  intro i j hij
  unfold flatsK at h
  rw [allNK_iff] at h
  have h1 := (allNK_iff _ _).1 (h j j.isLt) i hij
  unfold flatK at h1
  obtain ⟨c, hc, h2⟩ := (anyL_iff _ _).1 h1
  refine ⟨c, hc, fun l => ?_⟩
  have h3 := beqB_eq_true ((allNK_iff _ _).1 h2 l l.isLt)
  rw [decide_eq_true_iff, memK_iff] at h3
  exact h3

end CFSG.KC.E7T3

end
