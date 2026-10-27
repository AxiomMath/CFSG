module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6TwoData

public section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6Pack

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Curtis.UnitaryLevi
open CFSG.HardMathSupport.Malle.E27Lie.ExcCross

@[expose] def bandK (a b : Bool) : Bool := Bool.rec false b a

@[expose] def allNK (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k r => bandK (f k) r) n

@[expose] def anyNK (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k r => Bool.rec r true (f k)) n

@[expose] def BAD : ℕ := 281474976710656

@[expose] def lnK (x s : ℕ) : ℕ := Nat.land (Nat.shiftRight x s) 255

@[expose] def updK (x s old nw : ℕ) : ℕ :=
  Nat.add (Nat.sub x (Nat.shiftLeft old s)) (Nat.shiftLeft nw s)

@[expose] def setK (x s old c plus : ℕ) : ℕ :=
  Bool.rec BAD
    (Bool.rec BAD
      (Bool.rec BAD (updK x s old (Nat.sub plus (Nat.add old c)))
        (Nat.blt (Nat.sub plus (Nat.add old c)) 256))
      (Nat.ble (Nat.add old c) plus))
    (Nat.blt x BAD)

@[expose] def stepK (i x : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec
    (setK x 40 (lnK x 40) 0 (Nat.add (lnK x 32) 128))
    (setK x 32 (lnK x 32) 0 (Nat.add (lnK x 24) (lnK x 40))) (Nat.beq i 4))
    (setK x 24 (lnK x 24) 128 (Nat.add (Nat.add (lnK x 8) (lnK x 16)) (lnK x 32))) (Nat.beq i 3))
    (setK x 16 (lnK x 16) 0 (Nat.add (lnK x 0) (lnK x 24))) (Nat.beq i 2))
    (setK x 8 (lnK x 8) 0 (Nat.add (lnK x 24) 128)) (Nat.beq i 1))
    (setK x 0 (lnK x 0) 0 (Nat.add (lnK x 16) 128)) (Nat.beq i 0)

@[expose] def actK (l : List (Fin Tag.E6.rank)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) x (fun i _ r => stepK i.val r) l

@[expose] def ej (j : ℕ) : ℕ := Nat.add 141289400074368 (Nat.shiftLeft 1 (Nat.mul 8 j))

@[expose] def eqW (l l' : List (Fin Tag.E6.rank)) : Bool :=
  allNK 6 fun j => bandK (Nat.blt (actK l (ej j)) BAD) (Nat.beq (actK l (ej j)) (actK l' (ej j)))

@[expose] def neW (l l' : List (Fin Tag.E6.rank)) : Bool :=
  anyNK 6 fun j => bandK (Nat.blt (actK l (ej j)) BAD)
    (bandK (Nat.blt (actK l' (ej j)) BAD) (Bool.rec true false (Nat.beq (actK l (ej j)) (actK l' (ej j)))))

@[expose] def pairB (lx ly : List (Fin Tag.E6.rank)) : Bool :=
  bandK (eqW (lx ++ lx ++ lx) []) (bandK (eqW (ly ++ ly ++ ly) []) (bandK (eqW (lx ++ ly) (ly ++ lx))
    (bandK (neW lx []) (bandK (neW ly []) (bandK (neW ly lx) (neW ly (lx ++ lx)))))))

@[expose] def toV (x : ℕ) (j : Fin Tag.E6.rank) : ℤ := ((lnK x (8 * j.val) : ℕ) : ℤ) - 128

theorem bandK_eq (a b : Bool) : bandK a b = (a && b) := by cases a <;> rfl

theorem brec_eq {α : Sort _} (f t : α) (b : Bool) :
    (Bool.rec f t b : α) = if b = true then t else f := by
  cases b <;> rfl

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

theorem anyNK_iff (n : ℕ) (f : ℕ → Bool) : anyNK n f = true → ∃ k < n, f k = true := by
  induction n with
  | zero => intro h; exact absurd h (by simp [anyNK])
  | succ n ih =>
    intro h
    change (Bool.rec (anyNK n f) true (f n) : Bool) = true at h
    rw [brec_eq] at h
    by_cases hf : f n = true
    · exact ⟨n, Nat.lt_succ_self n, hf⟩
    · rw [if_neg hf] at h
      obtain ⟨k, hk, h'⟩ := ih h
      exact ⟨k, Nat.lt_succ_of_lt hk, h'⟩

theorem lnK_eq (x s : ℕ) : lnK x s = x / 2 ^ s % 256 := by
  unfold lnK
  change (x >>> s) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem BAD_eq : BAD = 2 ^ 48 := rfl

theorem shl_eq (a b : ℕ) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b

def pk (a0 a1 a2 a3 a4 a5 : ℕ) : ℕ :=
  a0 + 256 * a1 + 65536 * a2 + 16777216 * a3 + 4294967296 * a4 + 1099511627776 * a5

theorem exists_pk {x : ℕ} (hx : x < BAD) : ∃ a0 a1 a2 a3 a4 a5 : ℕ, a0 < 256 ∧ a1 < 256 ∧
    a2 < 256 ∧ a3 < 256 ∧ a4 < 256 ∧ a5 < 256 ∧ x = pk a0 a1 a2 a3 a4 a5 := by
  rw [BAD_eq] at hx
  refine ⟨x % 256, x / 256 % 256, x / 65536 % 256, x / 16777216 % 256, x / 4294967296 % 256,
    x / 1099511627776 % 256, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  unfold pk
  omega

section Lanes

variable {a0 a1 a2 a3 a4 a5 : ℕ} (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256)
  (h3 : a3 < 256) (h4 : a4 < 256) (h5 : a5 < 256)
include h0 h1 h2 h3 h4 h5

theorem pk_lt : pk a0 a1 a2 a3 a4 a5 < BAD := by
  rw [BAD_eq]
  unfold pk
  omega

theorem lnK_pk : lnK (pk a0 a1 a2 a3 a4 a5) 0 = a0 ∧ lnK (pk a0 a1 a2 a3 a4 a5) 8 = a1 ∧
    lnK (pk a0 a1 a2 a3 a4 a5) 16 = a2 ∧ lnK (pk a0 a1 a2 a3 a4 a5) 24 = a3 ∧
    lnK (pk a0 a1 a2 a3 a4 a5) 32 = a4 ∧ lnK (pk a0 a1 a2 a3 a4 a5) 40 = a5 := by
  simp only [lnK_eq, pk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem toV_pk : toV (pk a0 a1 a2 a3 a4 a5) =
    fun j : Fin 6 => ((![a0, a1, a2, a3, a4, a5] j : ℕ) : ℤ) - 128 := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  funext j
  fin_cases j <;> simp [toV, l0, l1, l2, l3, l4, l5] <;> rfl

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

@[expose] def cE6 : Fin 6 → Fin 6 → ℤ :=
  ![![2, 0, -1, 0, 0, 0], ![0, 2, 0, -1, 0, 0], ![-1, 0, 2, -1, 0, 0], ![0, -1, -1, 2, -1, 0],
    ![0, 0, 0, -1, 2, -1], ![0, 0, 0, 0, -1, 2]]

theorem cartan_cE6 : ∀ i j : Fin 6, Tag.E6.cartan i j = cE6 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

theorem reflect_apply (i j : Fin 6) (v : Fin Tag.E6.rank → ℤ) :
    reflect Tag.E6 i v j = v j - (v (0 : Fin 6) * cE6 i (0 : Fin 6) +
      v (1 : Fin 6) * cE6 i (1 : Fin 6) + v (2 : Fin 6) * cE6 i (2 : Fin 6) +
      v (3 : Fin 6) * cE6 i (3 : Fin 6) + v (4 : Fin 6) * cE6 i (4 : Fin 6) +
      v (5 : Fin 6) * cE6 i (5 : Fin 6)) * (Pi.single i (1 : ℤ) : Fin 6 → ℤ) j := by
  change v j - (∑ m : Fin 6, Tag.E6.cartan i m * v m) * ((Pi.single i (1 : ℤ) : Fin 6 → ℤ) j) = _
  simp only [cartan_cE6]
  rw [Fin.sum_univ_six]
  ring

theorem stepK_0 (x : ℕ) : stepK 0 x = setK x 0 (lnK x 0) 0 (Nat.add (lnK x 16) 128) := rfl
theorem stepK_1 (x : ℕ) : stepK 1 x = setK x 8 (lnK x 8) 0 (Nat.add (lnK x 24) 128) := rfl
theorem stepK_2 (x : ℕ) : stepK 2 x = setK x 16 (lnK x 16) 0 (Nat.add (lnK x 0) (lnK x 24)) := rfl
theorem stepK_3 (x : ℕ) : stepK 3 x =
    setK x 24 (lnK x 24) 128 (Nat.add (Nat.add (lnK x 8) (lnK x 16)) (lnK x 32)) := rfl
theorem stepK_4 (x : ℕ) : stepK 4 x =
    setK x 32 (lnK x 32) 0 (Nat.add (lnK x 24) (lnK x 40)) := rfl
theorem stepK_5 (x : ℕ) : stepK 5 x = setK x 40 (lnK x 40) 0 (Nat.add (lnK x 32) 128) := rfl

theorem spec0 (x : ℕ) (h : stepK 0 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 0 x) j = reflect Tag.E6 (0 : Fin 6) (toV x) j := by
  rw [stepK_0] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨l0, -, l2, -, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l0, l2] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a0 * 2 ^ 0 + (Nat.add a2 128 - (a0 + 0)) * 2 ^ 0 =
      pk (a2 + 128 - a0) a1 a2 a3 a4 a5 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk (by omega) h1 h2 h3 h4 h5]
  fin_cases j <;> simp [cE6] <;> omega

theorem spec1 (x : ℕ) (h : stepK 1 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 1 x) j = reflect Tag.E6 (1 : Fin 6) (toV x) j := by
  rw [stepK_1] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, l1, -, l3, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l1, l3] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a1 * 2 ^ 8 + (Nat.add a3 128 - (a1 + 0)) * 2 ^ 8 =
      pk a0 (a3 + 128 - a1) a2 a3 a4 a5 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk h0 (by omega) h2 h3 h4 h5]
  fin_cases j <;> simp [cE6] <;> omega

theorem spec2 (x : ℕ) (h : stepK 2 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 2 x) j = reflect Tag.E6 (2 : Fin 6) (toV x) j := by
  rw [stepK_2] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨l0, -, l2, l3, -, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l0, l2, l3] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a2 * 2 ^ 16 + (Nat.add a0 a3 - (a2 + 0)) * 2 ^ 16 =
      pk a0 a1 (a0 + a3 - a2) a3 a4 a5 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk h0 h1 (by omega) h3 h4 h5]
  fin_cases j <;> simp [cE6] <;> omega

set_option maxRecDepth 8000 in
theorem spec3 (x : ℕ) (h : stepK 3 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 3 x) j = reflect Tag.E6 (3 : Fin 6) (toV x) j := by
  rw [stepK_3] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, l1, l2, l3, l4, -⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l1, l2, l3, l4] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a3 * 2 ^ 24 +
      (Nat.add (Nat.add a1 a2) a4 - (a3 + 128)) * 2 ^ 24 =
      pk a0 a1 a2 (a1 + a2 + a4 - (a3 + 128)) a4 a5 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk h0 h1 h2 (by omega) h4 h5]
  fin_cases j <;> simp [cE6] <;> omega

theorem spec4 (x : ℕ) (h : stepK 4 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 4 x) j = reflect Tag.E6 (4 : Fin 6) (toV x) j := by
  rw [stepK_4] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, -, -, l3, l4, l5⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l3, l4, l5] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a4 * 2 ^ 32 + (Nat.add a3 a5 - (a4 + 0)) * 2 ^ 32 =
      pk a0 a1 a2 a3 (a3 + a5 - a4) a5 := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk h0 h1 h2 h3 (by omega) h5]
  fin_cases j <;> simp [cE6] <;> omega

theorem spec5 (x : ℕ) (h : stepK 5 x < BAD) :
    x < BAD ∧ ∀ j : Fin 6, toV (stepK 5 x) j = reflect Tag.E6 (5 : Fin 6) (toV x) j := by
  rw [stepK_5] at h ⊢
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk (setK_spec h).1
  obtain ⟨-, -, -, -, l4, l5⟩ := lnK_pk h0 h1 h2 h3 h4 h5
  rw [l4, l5] at h ⊢
  obtain ⟨-, e1, e2, he⟩ := setK_spec h
  simp only [Nat.add_eq] at e1 e2
  refine ⟨pk_lt h0 h1 h2 h3 h4 h5, fun j => ?_⟩
  have hp : pk a0 a1 a2 a3 a4 a5 - a5 * 2 ^ 40 + (Nat.add a4 128 - (a5 + 0)) * 2 ^ 40 =
      pk a0 a1 a2 a3 a4 (a4 + 128 - a5) := by
    unfold pk
    simp only [Nat.add_eq, Nat.reducePow]
    omega
  rw [he, hp, reflect_apply, toV_pk h0 h1 h2 h3 h4 h5, toV_pk h0 h1 h2 h3 h4 (by omega)]
  fin_cases j <;> simp [cE6] <;> omega

theorem stepK_spec (i : Fin Tag.E6.rank) (x : ℕ) (h : stepK i.val x < BAD) :
    x < BAD ∧ toV (stepK i.val x) = (Smat Tag.E6 i).mulVec (toV x) := by
  rw [← reflect_eq_mulVec]
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

theorem actK_spec (l : List (Fin Tag.E6.rank)) (x : ℕ) (h : actK l x < BAD) :
    x < BAD ∧ toV (actK l x) = (mp6 l).mulVec (toV x) := by
  induction l with
  | nil => exact ⟨h, (Matrix.one_mulVec (toV x)).symm⟩
  | cons i l ih =>
    change stepK i.val (actK l x) < BAD at h
    obtain ⟨h1, h2⟩ := stepK_spec i _ h
    obtain ⟨h3, h4⟩ := ih h1
    refine ⟨h3, ?_⟩
    change toV (stepK i.val (actK l x)) = _
    rw [h2, h4, mp6, mp6, List.map_cons, List.prod_cons]
    exact Matrix.mulVec_mulVec _ _ _

theorem toV_inj {x y : ℕ} (hx : x < BAD) (hy : y < BAD) (h : toV x = toV y) : x = y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, h0, h1, h2, h3, h4, h5, rfl⟩ := exists_pk hx
  obtain ⟨b0, b1, b2, b3, b4, b5, g0, g1, g2, g3, g4, g5, rfl⟩ := exists_pk hy
  rw [toV_pk h0 h1 h2 h3 h4 h5, toV_pk g0 g1 g2 g3 g4 g5] at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  have e4 := congrFun h 4
  have e5 := congrFun h 5
  simp at e0 e1 e2 e3 e4 e5
  unfold pk
  omega

theorem toV_ej (j : Fin 6) : toV (ej j.val) = Pi.single j 1 := by
  funext k
  fin_cases j <;> fin_cases k <;> decide +kernel

theorem ej_lt : ∀ j : Fin 6, ej j.val < BAD := by decide +kernel

theorem col_of {l : List (Fin Tag.E6.rank)} {j : Fin 6} (h : actK l (ej j.val) < BAD) :
    toV (actK l (ej j.val)) = (mp6 l).col j := by
  rw [(actK_spec l _ h).2, toV_ej]
  exact Matrix.mulVec_single_one _ _

theorem eqW_spec {l l' : List (Fin Tag.E6.rank)} (h : eqW l l' = true) : mp6 l = mp6 l' := by
  unfold eqW at h
  rw [allNK_iff] at h
  ext r j
  have hj := h j.val j.isLt
  rw [bandK_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hj
  obtain ⟨hlt, heq⟩ := hj
  have e1 := col_of hlt
  rw [heq] at hlt e1
  have e2 := col_of (l := l') hlt
  have := congrFun (e1.symm.trans e2) r
  simpa [Matrix.col_apply] using this

theorem neW_spec {l l' : List (Fin Tag.E6.rank)} (h : neW l l' = true) : mp6 l ≠ mp6 l' := by
  unfold neW at h
  obtain ⟨k, hk, h⟩ := anyNK_iff _ _ h
  rw [bandK_eq, bandK_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  intro hm
  have e1 := col_of (l := l) (j := ⟨k, hk⟩) h1
  have e2 := col_of (l := l') (j := ⟨k, hk⟩) h2
  rw [hm, ← e2] at e1
  have := toV_inj h1 h2 e1
  rw [this, Nat.beq_refl] at h3
  exact absurd h3 (by decide)

theorem pairOK6_of_pairB {lx ly : List (Fin Tag.E6.rank)} (h : pairB lx ly = true) :
    PairOK6 lx ly := by
  unfold pairB at h
  simp only [bandK_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨eqW_spec h1, eqW_spec h2, eqW_spec h3, neW_spec h4, neW_spec h5, neW_spec h6, neW_spec h7⟩

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross.E6Pack

end
