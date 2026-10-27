module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Set.Card
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] def linL (c : Array Nat) (v : Nat) (l : List Nat) : Nat :=
  l.foldr (fun i acc => if v.testBit i then c[i]! ^^^ acc else acc) 0

@[expose] def lin (c : Array Nat) (v : Nat) : Nat := linL c v (List.range 10)

@[expose] def compose (c c' : Array Nat) : Array Nat := Array.ofFn (n := 10) fun i => lin c c'[i]!

@[expose] def idCols : Array Nat := Array.ofFn (n := 10) fun i => 2 ^ i.val

theorem linL_xor (c : Array Nat) (v w : Nat) (l : List Nat) :
    linL c (v ^^^ w) l = linL c v l ^^^ linL c w l := by
  induction l with
  | nil => simp [linL]
  | cons i l ih =>
    simp only [linL, List.foldr_cons] at ih ⊢
    rw [ih, Nat.testBit_xor]
    cases hv : v.testBit i <;> cases hw : w.testBit i <;>
      simp [Nat.xor_assoc, Nat.xor_left_comm, Nat.xor_comm]

theorem lin_xor (c : Array Nat) (v w : Nat) : lin c (v ^^^ w) = lin c v ^^^ lin c w :=
  linL_xor c v w _

theorem linL_zero (c : Array Nat) (l : List Nat) : linL c 0 l = 0 := by
  induction l with
  | nil => simp [linL]
  | cons i l ih => simp_all [linL]

theorem lin_zero (c : Array Nat) : lin c 0 = 0 := linL_zero c _

theorem linL_two_pow_of_notMem (c : Array Nat) {i : Nat} {l : List Nat} (hi : i ∉ l) :
    linL c (2 ^ i) l = 0 := by
  induction l with
  | nil => simp [linL]
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    simp only [linL, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_two_pow]
    simp [hij, ih hil]

theorem linL_two_pow (c : Array Nat) {i : Nat} {l : List Nat} (hl : l.Nodup) (hi : i ∈ l) :
    linL c (2 ^ i) l = c[i]! := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    by_cases hij : i = j
    · subst hij
      have h0 := linL_two_pow_of_notMem c hl.1
      simp only [linL, List.foldr_cons] at h0 ⊢
      rw [Nat.testBit_two_pow]
      simp [h0]
    · have hil : i ∈ l := by simpa [hij] using hi
      have h1 := ih hl.2 hil
      simp only [linL, List.foldr_cons] at h1 ⊢
      rw [Nat.testBit_two_pow]
      simp [hij, h1]

theorem lin_two_pow (c : Array Nat) {i : Nat} (hi : i < 10) : lin c (2 ^ i) = c[i]! :=
  linL_two_pow c (List.nodup_range) (List.mem_range.2 hi)

theorem linL_lt (c : Array Nat) (h : ∀ i < 10, c[i]! < 1024) (v : Nat) (l : List Nat)
    (hl : ∀ i ∈ l, i < 10) : linL c v l < 1024 := by
  induction l with
  | nil => simp [linL]
  | cons i l ih =>
    simp only [linL, List.foldr_cons]
    have h1 := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have h2 := h i (hl i List.mem_cons_self)
    split_ifs
    · exact Nat.xor_lt_two_pow (n := 10) h2 h1
    · exact h1

theorem lin_lt (c : Array Nat) (h : ∀ i < 10, c[i]! < 1024) (v : Nat) : lin c v < 1024 :=
  linL_lt c h v _ fun _ hi => List.mem_range.1 hi

theorem compose_getElem! (c c' : Array Nat) {i : Nat} (hi : i < 10) :
    (compose c c')[i]! = lin c c'[i]! := by
  unfold compose
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rfl

theorem compose_lt {c : Array Nat} (hc : ∀ i < 10, c[i]! < 1024) (c' : Array Nat) :
    ∀ i < 10, (compose c c')[i]! < 1024 := fun i hi => by
  rw [compose_getElem! c c' hi]
  exact lin_lt c hc _

theorem linL_compose (c c' : Array Nat) (v : Nat) (l : List Nat) (hl : ∀ i ∈ l, i < 10) :
    linL (compose c c') v l = lin c (linL c' v l) := by
  induction l with
  | nil => simp [linL, lin_zero]
  | cons i l ih =>
    have h1 := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hi := hl i List.mem_cons_self
    simp only [linL, List.foldr_cons] at h1 ⊢
    rw [h1]
    split_ifs
    · rw [lin_xor, compose_getElem! c c' hi]
    · rfl

theorem lin_compose (c c' : Array Nat) (v : Nat) :
    lin (compose c c') v = lin c (lin c' v) :=
  linL_compose c c' v _ fun _ hi => List.mem_range.1 hi

set_option maxRecDepth 100000 in
theorem lin_idCols_aux : ∀ v : Fin 1024, lin idCols v.val = v.val := by decide

theorem lin_idCols {v : Nat} (hv : v < 1024) : lin idCols v = v :=
  lin_idCols_aux ⟨v, hv⟩

theorem idCols_lt : ∀ i < 10, idCols[i]! < 1024 := fun i hi => by
  unfold idCols
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have h : 2 ^ i < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hi
  exact lt_of_lt_of_eq h (by norm_num)

section Phi

variable {G : Type*} [Group G] (b : ℕ → G)

@[expose] def phiL (v : ℕ) (l : List ℕ) : G :=
  l.foldr (fun i acc => if v.testBit i then b i * acc else acc) 1

@[expose] def phi (v : ℕ) : G := phiL b v (List.range 10)

variable {b}

theorem phiL_comm (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i) (v : ℕ) {l : List ℕ}
    (hl : ∀ i ∈ l, i < 10) {j : ℕ} (hj : j < 10) : b j * phiL b v l = phiL b v l * b j := by
  induction l with
  | nil => simp [phiL]
  | cons i l ih =>
    have h1 := ih fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have hi := hl i List.mem_cons_self
    simp only [phiL, List.foldr_cons] at h1 ⊢
    split_ifs
    · rw [← mul_assoc, hb j hj i hi, mul_assoc, h1, mul_assoc]
    · exact h1

theorem phiL_cons (v i : ℕ) (l : List ℕ) :
    phiL b v (i :: l) = if v.testBit i then b i * phiL b v l else phiL b v l := rfl

theorem phiL_xor (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) (v w : ℕ) {l : List ℕ} (hl : ∀ i ∈ l, i < 10) :
    phiL b (v ^^^ w) l = phiL b v l * phiL b w l := by
  induction l with
  | nil => simp [phiL]
  | cons i l ih =>
    have h1 := ih fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have hi := hl i List.mem_cons_self
    have hc := phiL_comm hb v (l := l) (fun k hk => hl k (List.mem_cons_of_mem _ hk)) hi
    have hs := hsq i hi
    rw [phiL_cons, phiL_cons, phiL_cons, h1, Nat.testBit_xor]
    generalize phiL b v l = A at hc ⊢
    generalize phiL b w l = B
    cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp
    · calc b i * (A * B) = b i * A * B := (mul_assoc _ _ _).symm
        _ = A * b i * B := by rw [hc]
        _ = A * (b i * B) := mul_assoc _ _ _
    · exact (mul_assoc _ _ _).symm
    · calc A * B = A * (b i * b i * B) := by rw [hs, one_mul]
        _ = A * (b i * (b i * B)) := by rw [mul_assoc]
        _ = A * b i * (b i * B) := (mul_assoc _ _ _).symm
        _ = b i * A * (b i * B) := by rw [hc]

theorem phiL_zero (l : List ℕ) : phiL b 0 l = 1 := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [phiL_cons, ih]; simp

theorem phi_zero : phi b 0 = 1 := phiL_zero _

theorem phi_xor (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) (v w : ℕ) : phi b (v ^^^ w) = phi b v * phi b w :=
  phiL_xor hb hsq v w fun _ hi => List.mem_range.1 hi

theorem phi_sq (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) (v : ℕ) : phi b v * phi b v = 1 := by
  rw [← phi_xor hb hsq, Nat.xor_self, phi_zero]

theorem phiL_two_pow_of_notMem {i : ℕ} {l : List ℕ} (hi : i ∉ l) : phiL b (2 ^ i) l = 1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (h ▸ List.mem_cons_self)
    have hil : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
    rw [phiL_cons, Nat.testBit_two_pow]
    simp [hij, ih hil]

theorem phiL_two_pow {i : ℕ} {l : List ℕ} (hl : l.Nodup) (hi : i ∈ l) :
    phiL b (2 ^ i) l = b i := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    rw [phiL_cons, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij
      simp [phiL_two_pow_of_notMem hl.1]
    · have hil : i ∈ l := by simpa [hij] using hi
      simp [hij, ih hl.2 hil]

theorem phi_two_pow {i : ℕ} (hi : i < 10) : phi b (2 ^ i) = b i :=
  phiL_two_pow List.nodup_range (List.mem_range.2 hi)

theorem phiL_mem (v : ℕ) {l : List ℕ} (hl : ∀ i ∈ l, i < 10) :
    phiL b v l ∈ Subgroup.closure (b '' Set.Iio 10) := by
  induction l with
  | nil => exact Subgroup.one_mem _
  | cons i l ih =>
    rw [phiL_cons]
    have h1 := ih fun k hk => hl k (List.mem_cons_of_mem _ hk)
    split_ifs
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, hl i List.mem_cons_self, rfl⟩) h1
    · exact h1

theorem phi_mem (v : ℕ) : phi b v ∈ Subgroup.closure (b '' Set.Iio 10) :=
  phiL_mem v fun _ hi => List.mem_range.1 hi

theorem exists_phi_of_mem_closure (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) {x : G} (hx : x ∈ Subgroup.closure (b '' Set.Iio 10)) :
    ∃ v < 1024, phi b v = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨2 ^ i, ?_, phi_two_pow hi⟩
    have h : 2 ^ i < 2 ^ 10 := Nat.pow_lt_pow_right (by norm_num) hi
    exact lt_of_lt_of_eq h (by norm_num)
  | one => exact ⟨0, by norm_num, phi_zero⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨v ^^^ w, Nat.xor_lt_two_pow (n := 10) hv hw, phi_xor hb hsq v w⟩
  | inv x _ hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, hv, (inv_eq_of_mul_eq_one_right (phi_sq hb hsq v)).symm⟩

theorem conj_phiL (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) (t : G) (c : Array ℕ)
    (hc : ∀ i < 10, t * b i * t⁻¹ = phi b c[i]!) (v : ℕ) {l : List ℕ} (hl : ∀ i ∈ l, i < 10) :
    t * phiL b v l * t⁻¹ = phi b (linL c v l) := by
  induction l with
  | nil => simp [phiL, linL, phi_zero]
  | cons i l ih =>
    have h1 := ih fun k hk => hl k (List.mem_cons_of_mem _ hk)
    have hi := hl i List.mem_cons_self
    have e2 : linL c v (i :: l) = if v.testBit i then c[i]! ^^^ linL c v l else linL c v l := rfl
    rw [phiL_cons, e2]
    split_ifs
    · rw [phi_xor hb hsq, ← hc i hi, ← h1]
      group
    · exact h1

theorem conj_phi (hb : ∀ i < 10, ∀ j < 10, b i * b j = b j * b i)
    (hsq : ∀ i < 10, b i * b i = 1) (t : G) (c : Array ℕ)
    (hc : ∀ i < 10, t * b i * t⁻¹ = phi b c[i]!) (v : ℕ) :
    t * phi b v * t⁻¹ = phi b (lin c v) :=
  conj_phiL hb hsq t c hc v fun _ hi => List.mem_range.1 hi

end Phi

@[expose] def fn (c : Array ℕ) (v : Fin 1024) : Fin 1024 :=
  ⟨lin c v.val % 1024, Nat.mod_lt _ (by norm_num)⟩

theorem fn_val {c : Array ℕ} (hc : ∀ i < 10, c[i]! < 1024) (v : Fin 1024) :
    (fn c v).val = lin c v.val :=
  Nat.mod_eq_of_lt (lin_lt c hc _)

theorem fn_compose {c c' : Array ℕ} (hc : ∀ i < 10, c[i]! < 1024)
    (hc' : ∀ i < 10, c'[i]! < 1024) : fn (compose c c') = fn c ∘ fn c' := by
  funext v
  apply Fin.ext
  rw [fn_val (compose_lt hc c'), Function.comp_apply, fn_val hc, fn_val hc', lin_compose]

theorem fn_idCols : fn idCols = id := by
  funext v
  apply Fin.ext
  rw [fn_val idCols_lt, lin_idCols v.isLt]
  rfl

theorem col_eq_of_fn_eq {c c' : Array ℕ} (hc : ∀ i < 10, c[i]! < 1024)
    (hc' : ∀ i < 10, c'[i]! < 1024) (h : fn c = fn c') {i : ℕ} (hi : i < 10) : c[i]! = c'[i]! := by
  have h2 : 2 ^ i < 1024 := lt_of_lt_of_eq (Nat.pow_lt_pow_right (by norm_num) hi) (by norm_num)
  have := congrArg (fun f => (f ⟨2 ^ i, h2⟩ : Fin 1024).val) h
  simp only [fn_val hc, fn_val hc', lin_two_pow c hi, lin_two_pow c' hi] at this
  exact this

@[expose] def mset (cu cw : Array (Array ℕ)) : Set (Fin 1024 → Fin 1024) :=
  {f | ∃ k0 < cu.size, ∃ k1 < cw.size, f = fn (compose cu[k0]! cw[k1]!)}

open Classical in
@[expose] noncomputable def fixSet (X : Finset (Fin 1024 → Fin 1024)) : Finset (Fin 1024) :=
  Finset.univ.filter fun v => ∀ x ∈ X, x v = v

@[expose] def fcSpec (cu cw : Array (Array ℕ)) : Prop :=
  2 ^ 7 ≤ (mset cu cw).ncard ∧
    ∀ X : Finset (Fin 1024 → Fin 1024), (X : Set (Fin 1024 → Fin 1024)) ⊆ mset cu cw →
      (∀ x ∈ X, ∀ y ∈ X, x ∘ y ∈ X) → (∀ x ∈ X, x ∘ x = id) → X.Nonempty →
      (∀ x ∈ X, x = id) ∨ X.card * (fixSet X).card ≤ 2 ^ 9

end CFSG.EvenSporadicStandard.TwoFi22.DS81
