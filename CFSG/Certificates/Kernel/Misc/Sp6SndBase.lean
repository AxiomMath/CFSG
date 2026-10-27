module

public import Certificates.Data.Kernel.Misc.Sp6
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqData
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.NeZero

public section

namespace CFSG.KC.Misc.Sp6.Snd

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62 CFSG.KC.Misc.Sp6
open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_eq_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

theorem impB_eq_true {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

theorem letN_eq (y : ℕ) (k : ℕ → ℕ) : letN y k = k y := by cases y <;> rfl

theorem allN_eq_true {m : ℕ} {f : ℕ → Bool} : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [show allN 0 f = true from rfl]
  | succ m ih =>
    rw [show allN (m + 1) f = andB (f m) (allN m f) from rfl, andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hlt : i < m
      · exact h2 i hlt
      · have him : i = m := by omega
        rw [him]; exact h1
    · intro h
      exact ⟨h m (by omega), fun i hi => h i (by omega)⟩

theorem anyN_eq_true {m : ℕ} {f : ℕ → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [show anyN 0 f = false from rfl]
  | succ m ih =>
    rw [show anyN (m + 1) f = orB (f m) (anyN m f) from rfl, orB_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, by omega, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      by_cases hlt : i < m
      · exact Or.inr ⟨i, hlt, h⟩
      · have him : i = m := by omega
        rw [him] at h; exact Or.inl h

theorem allL_eq_true {l : List ℕ} {f : ℕ → Bool} : allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => simp [show allL [] f = true from rfl]
  | cons x t ih =>
    rw [show allL (x :: t) f = andB (f x) (allL t f) from rfl, andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact h2 y hy
    · intro h
      exact ⟨h x (by simp), fun y hy => h y (by simp [hy])⟩

theorem allLL_eq_true {L : List (List ℕ)} {f : List ℕ → Bool} :
    allLL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [show allLL [] f = true from rfl]
  | cons x t ih =>
    rw [show allLL (x :: t) f = andB (f x) (allLL t f) from rfl, andB_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1
      · exact h2 y hy
    · intro h
      exact ⟨h x (by simp), fun y hy => h y (by simp [hy])⟩

theorem lenN_eq (l : List ℕ) : lenN l = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    show Nat.succ (lenN t) = _
    rw [ih]; rfl

theorem memN_eq_true {x : ℕ} {l : List ℕ} : memN x l = true ↔ x ∈ l := by
  have key : ∀ l : List ℕ, List.rec (motive := fun _ => Bool) false
      (fun z _ ih => orB (Nat.beq x z) ih) l = true ↔ x ∈ l := by
    intro l
    induction l with
    | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd h (by simp)⟩
    | cons z t ih =>
      show orB (Nat.beq x z) (List.rec (motive := fun _ => Bool) false
        (fun z _ ih => orB (Nat.beq x z) ih) t) = true ↔ _
      rw [orB_eq_true, ih]
      constructor
      · rintro (h | h)
        · exact List.mem_cons.mpr (Or.inl (Nat.eq_of_beq_eq_true h))
        · exact List.mem_cons.mpr (Or.inr h)
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h
  rw [memN, letB_eq]
  exact key l

theorem eqLN_eq_true {a b : List ℕ} : eqLN a b = true ↔ a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | cons y s => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd h (by simp)⟩
  | cons x t ih =>
    cases b with
    | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => absurd h (by simp)⟩
    | cons y s =>
      show andB (Nat.beq x y) (eqLN t s) = true ↔ x :: t = y :: s
      rw [andB_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩
        have hxy : x = y := Nat.eq_of_beq_eq_true h1
        rw [hxy, h2]
      · intro h
        injection h with hxy hts
        exact ⟨by simp [hxy], hts⟩

theorem nthN_eq (l : List ℕ) (i : ℕ) : nthN l i = l.getD i 0 := by
  induction l generalizing i with
  | nil => show (0 : ℕ) = _; simp
  | cons x t ih =>
    cases i with
    | zero => show x = _; simp
    | succ j => show nthN t j = _; rw [ih]; simp

theorem gensK_eq (G : List (List ℕ)) : gensK G = G.map codeL := by
  induction G with
  | nil => rfl
  | cons g t ih =>
    show codeL g :: gensK t = codeL g :: t.map codeL
    rw [ih]

theorem invsL_eq (l : List ℕ) : invsL l = l.filter invK := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    show Bool.rec (motive := fun _ => List ℕ) (invsL t) (x :: invsL t) (invK x)
      = (x :: t).filter invK
    rw [ih]
    simp only [List.filter_cons]
    cases hx : invK x <;> rfl

theorem hasB_eq (M i : ℕ) : hasB M i = M.testBit i := by
  have key : M &&& (1 <<< i) = if M.testBit i then 2 ^ i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.shiftLeft_eq, one_mul]
    by_cases hij : i = j
    · subst hij; cases hM : M.testBit i <;> simp [hM]
    · cases hM : M.testBit i <;> simp [hM, hij, Nat.testBit_two_pow]
  show Nat.blt 0 (M &&& (1 <<< i)) = M.testBit i
  rw [key]
  cases h : M.testBit i
  · rfl
  · simp only [h, ↓reduceIte, Nat.blt_eq]
    exact Nat.two_pow_pos i

theorem bitK_eq (x k : ℕ) : bitK x k = if x.testBit k then 1 else 0 := by
  show x >>> k &&& 1 = _
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ k) with h | h <;> simp [h]

theorem popN_eq (M n : ℕ) : popN M n = ((List.range n).filter fun i => M.testBit i).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show popN M n + bitK M n = _
    rw [ih, bitK_eq, List.range_succ, List.filter_append, List.length_append]
    by_cases h : M.testBit n <;> simp [h]

theorem land_mask_eq_zero_iff {A C : ℕ} (hA : A < 2 ^ 128) :
    Nat.land A (Nat.xor C 340282366920938463463374607431768211455) = 0 ↔
      ∀ i, A.testBit i = true → C.testBit i = true := by
  have hM : (340282366920938463463374607431768211455 : ℕ) = 2 ^ 128 - 1 := by decide
  have hlt : ∀ i, A.testBit i = true → i < 128 := by
    intro i hi
    by_contra hc
    have h0 : A.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by decide) (not_lt.mp hc)))
    exact absurd (hi.symm.trans h0) (by decide)
  show (A &&& (C ^^^ 340282366920938463463374607431768211455)) = 0 ↔ _
  rw [hM]
  constructor
  · intro h i hi
    have h2 := congrArg (fun n => Nat.testBit n i) h
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit,
      hi, Bool.true_and] at h2
    have hi128 := hlt i hi
    simpa [hi128] using h2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hi : A.testBit i = true
    · have hi128 := hlt i hi
      simp [hi, h i hi, hi128]
    · simp at hi
      simp [hi]

@[expose] def IsTup (l : List ℕ) : Prop := l.length = 6 ∧ ∀ x ∈ l, x < 64

@[expose] noncomputable def dec (A : ℕ) : List ℕ := (List.range 6).map (imgK A)

theorem tupOK_iff {l : List ℕ} : tupOK l = true ↔ IsTup l := by
  show andB (Nat.beq (lenN l) 6) (allL l fun x => Nat.blt x 64) = true ↔ IsTup l
  rw [andB_eq_true, lenN_eq, allL_eq_true]
  simp [IsTup]

theorem codeL_eq_codeT (l : List ℕ) : codeL l = codeT l := by
  have key : ∀ (l : List ℕ) (acc : ℕ),
      List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
        (fun x _ ih acc => ih (Nat.add (Nat.mul (nat_lit 64) acc) x)) l acc
        = l.foldl (fun r a => 64 * r + a) acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons x t ih => intro acc; exact ih (64 * acc + x)
  exact key l 0

end CFSG.KC.Misc.Sp6.Snd

end
