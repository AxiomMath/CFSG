module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Find
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSmallLie.FFourTwo.Pc

open scoped commutatorElement

@[expose] def lowIdx (m : ℕ) : ℕ := Nat.log2 (m &&& (m ^^^ (m - 1)))

@[expose] def dropLow (m : ℕ) : ℕ := m &&& (m - 1)

@[expose] def LowZero (k m : ℕ) : Prop := ∀ j < k, m.testBit j = false

theorem exists_lowest {m : ℕ} (hm : m ≠ 0) :
    ∃ p, m.testBit p = true ∧ ∀ j < p, m.testBit j = false := by
  classical
  have h : ∃ i, m.testBit i = true := Nat.exists_testBit_of_ne_zero hm
  refine ⟨Nat.find h, Nat.find_spec h, fun j hj => ?_⟩
  have := Nat.find_min h hj
  simpa using this

theorem mod_two_pow_succ_of_lowest {m p : ℕ} (hp : m.testBit p = true)
    (hlow : ∀ j < p, m.testBit j = false) : m % 2 ^ (p + 1) = 2 ^ p := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases hj : j < p
  · rw [hlow j hj]; simp; omega
  · by_cases hjp : j = p
    · subst hjp; simp [hp]
    · have : ¬ j < p + 1 := by omega
      simp [this]; omega

theorem testBit_sub_one_of_lowest {m p : ℕ} (hp : m.testBit p = true)
    (hlow : ∀ j < p, m.testBit j = false) (j : ℕ) :
    (m - 1).testBit j = if j < p then true else if j = p then false else m.testBit j := by
  have hm := Nat.div_add_mod m (2 ^ (p + 1))
  rw [mod_two_pow_succ_of_lowest hp hlow] at hm
  set q := m / 2 ^ (p + 1)
  have h1 : m - 1 = 2 ^ (p + 1) * q + (2 ^ p - 1) := by
    have : 1 ≤ 2 ^ p := Nat.one_le_two_pow
    omega
  have hlt' : 2 ^ p < 2 ^ (p + 1) := by
    have := Nat.two_pow_pos p
    rw [pow_succ]; omega
  have hlt : 2 ^ p - 1 < 2 ^ (p + 1) := by omega
  rw [h1, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_sub_one]
  have hmj : m.testBit j = if j < p + 1 then (2 ^ p).testBit j else q.testBit (j - (p + 1)) := by
    conv_lhs => rw [← hm]
    rw [Nat.testBit_two_pow_mul_add _ hlt']
  by_cases hj : j < p
  · have : j < p + 1 := by omega
    simp [hj, this]
  · by_cases hjp : j = p
    · subst hjp; simp
    · have : ¬ j < p + 1 := by omega
      simp only [this, ite_false] at hmj
      simp [hj, hjp, this, hmj]

theorem and_xor_sub_one_of_lowest {m p : ℕ} (hp : m.testBit p = true)
    (hlow : ∀ j < p, m.testBit j = false) : m &&& (m ^^^ (m - 1)) = 2 ^ p := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_and, Nat.testBit_xor, testBit_sub_one_of_lowest hp hlow, Nat.testBit_two_pow]
  by_cases hj : j < p
  · simp [hj, hlow j hj]; omega
  · by_cases hjp : j = p
    · subst hjp; simp [hp]
    · simp [hj, hjp]; omega

theorem lowIdx_eq {m p : ℕ} (hp : m.testBit p = true) (hlow : ∀ j < p, m.testBit j = false) :
    lowIdx m = p := by
  rw [lowIdx, and_xor_sub_one_of_lowest hp hlow, Nat.log2_two_pow]

theorem testBit_lowIdx {m : ℕ} (hm : m ≠ 0) : m.testBit (lowIdx m) = true := by
  obtain ⟨p, hp, hlow⟩ := exists_lowest hm
  rw [lowIdx_eq hp hlow]
  exact hp

theorem testBit_lt_lowIdx {m : ℕ} (hm : m ≠ 0) {j : ℕ} (hj : j < lowIdx m) :
    m.testBit j = false := by
  obtain ⟨p, hp, hlow⟩ := exists_lowest hm
  rw [lowIdx_eq hp hlow] at hj
  exact hlow j hj

theorem testBit_dropLow {m : ℕ} (hm : m ≠ 0) (j : ℕ) :
    (dropLow m).testBit j = (m.testBit j && decide (j ≠ lowIdx m)) := by
  obtain ⟨p, hp, hlow⟩ := exists_lowest hm
  rw [lowIdx_eq hp hlow, dropLow, Nat.testBit_and, testBit_sub_one_of_lowest hp hlow]
  by_cases hj : j < p
  · simp [hj, hlow j hj]
  · by_cases hjp : j = p
    · subst hjp; simp
    · simp [hj, hjp]

theorem dropLow_lt {m : ℕ} (hm : m ≠ 0) : dropLow m < m := by
  have h1 : dropLow m ≤ m := Nat.and_le_left
  refine lt_of_le_of_ne h1 fun h => ?_
  have h2 := testBit_dropLow hm (lowIdx m)
  rw [h, testBit_lowIdx hm] at h2
  simp at h2

theorem lowZero_zero (k : ℕ) : LowZero k 0 := fun j _ => Nat.zero_testBit j

theorem lowZero_of_le {k k' m : ℕ} (h : LowZero k m) (hk : k' ≤ k) : LowZero k' m :=
  fun j hj => h j (by omega)

theorem le_lowIdx_of_lowZero {k m : ℕ} (hm : m ≠ 0) (h : LowZero k m) : k ≤ lowIdx m := by
  by_contra hlt
  have := h (lowIdx m) (by omega)
  rw [testBit_lowIdx hm] at this
  exact absurd this (by decide)

theorem lowZero_dropLow {k m : ℕ} (h : LowZero k m) : LowZero k (dropLow m) := by
  intro j hj
  by_cases hm : m = 0
  · subst hm; simp [dropLow]
  · rw [testBit_dropLow hm, h j hj, Bool.false_and]

theorem lt_two_pow_dropLow {m n : ℕ} (h : m < 2 ^ n) : dropLow m < 2 ^ n :=
  lt_of_le_of_lt Nat.and_le_left h

variable {G : Type*} [Group G]

@[expose] def nf (g : ℕ → G) (E : ℕ) : G :=
  if _h : E = 0 then 1 else g (lowIdx E) * nf g (dropLow E)
termination_by E
decreasing_by exact dropLow_lt _h

theorem nf_zero (g : ℕ → G) : nf g 0 = 1 := by
  rw [nf]; simp

theorem nf_of_ne (g : ℕ → G) {E : ℕ} (hE : E ≠ 0) :
    nf g E = g (lowIdx E) * nf g (dropLow E) := by
  rw [nf]; simp [hE]

theorem nf_or (g : ℕ → G) {a : ℕ} {F : ℕ} (hF : LowZero a F) :
    ∀ E, E < 2 ^ a → nf g (E ||| F) = nf g E * nf g F := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    by_cases h0 : E = 0
    · subst h0; rw [Nat.zero_or, nf_zero, one_mul]
    have hpE := testBit_lowIdx h0
    have hpa : lowIdx E < a := by
      by_contra hc
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by omega)
        (by omega : a ≤ lowIdx E)))] at hpE
      exact absurd hpE (by decide)
    have hor0 : E ||| F ≠ 0 := by
      intro h
      have := congrArg (fun m => m.testBit (lowIdx E)) h
      simp [Nat.testBit_or, hpE] at this
    have hlow : lowIdx (E ||| F) = lowIdx E := by
      refine lowIdx_eq (by rw [Nat.testBit_or, hpE, Bool.true_or]) fun j hj => ?_
      rw [Nat.testBit_or, testBit_lt_lowIdx h0 hj, hF j (by omega), Bool.false_or]
    have hdrop : dropLow (E ||| F) = dropLow E ||| F := by
      refine Nat.eq_of_testBit_eq fun j => ?_
      rw [testBit_dropLow hor0, hlow, Nat.testBit_or, Nat.testBit_or, testBit_dropLow h0]
      by_cases hj : j = lowIdx E
      · subst hj; simp [hF _ hpa]
      · simp [hj]
    rw [nf_of_ne g hor0, hlow, hdrop, ih _ (dropLow_lt h0) (lt_two_pow_dropLow hE), nf_of_ne g h0,
      mul_assoc]

theorem nf_two_pow (g : ℕ → G) (k : ℕ) : nf g (2 ^ k) = g k := by
  have h0 : (2 : ℕ) ^ k ≠ 0 := (Nat.two_pow_pos k).ne'
  have hk : lowIdx (2 ^ k) = k :=
    lowIdx_eq (by rw [Nat.testBit_two_pow]; simp) fun j hj => by
      rw [Nat.testBit_two_pow]; simp; omega
  have hd : dropLow (2 ^ k) = 0 := by
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [testBit_dropLow h0, hk, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : k = j <;> simp [hj]
  rw [nf_of_ne g h0, hk, hd, nf_zero, mul_one]

theorem eq_split (E i : ℕ) :
    E = E % 2 ^ i ||| ((E &&& 2 ^ i) ||| (E >>> (i + 1)) <<< (i + 1)) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_two_pow,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h1 : j < i
  · simp [h1]; omega
  · by_cases h2 : j = i
    · subst h2; simp
    · have h3 : j ≥ i + 1 := by omega
      have h4 : i + 1 + (j - (i + 1)) = j := by omega
      simp [h1, h3, h4]; omega

section Collector

variable (cm : ℕ → ℕ → ℕ)

mutual
@[expose] def mg : ℕ → ℕ → ℕ → ℕ
  | 0, E, _ => E
  | f + 1, E, i => tl f i (E % 2 ^ i ||| ((E ^^^ 2 ^ i) &&& 2 ^ i)) ((E >>> (i + 1)) <<< (i + 1))
termination_by f _ _ => (2 * f, 0, 0)

@[expose] def tl (f i r t : ℕ) : ℕ :=
  if _h : t = 0 then r else tl f i (mw f (mg f r (lowIdx t)) (cm (lowIdx t) i)) (dropLow t)
termination_by (2 * f + 1, 1, t)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
    | exact Prod.Lex.right _ (Prod.Lex.right _ (dropLow_lt _h))

@[expose] def mw (f E w : ℕ) : ℕ :=
  if _h : w = 0 then E else mw f (mg f E (lowIdx w)) (dropLow w)
termination_by (2 * f + 1, 0, w)
decreasing_by
  all_goals first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
    | exact Prod.Lex.right _ (Prod.Lex.right _ (dropLow_lt _h))
end

theorem mg_zero (E i : ℕ) : mg cm 0 E i = E := by rw [mg]

theorem mg_succ (f E i : ℕ) :
    mg cm (f + 1) E i =
      tl cm f i (E % 2 ^ i ||| ((E ^^^ 2 ^ i) &&& 2 ^ i)) ((E >>> (i + 1)) <<< (i + 1)) := by
  rw [mg]

theorem tl_zero (f i r : ℕ) : tl cm f i r 0 = r := by rw [tl]; simp

theorem tl_of_ne (f i r : ℕ) {t : ℕ} (ht : t ≠ 0) :
    tl cm f i r t = tl cm f i (mw cm f (mg cm f r (lowIdx t)) (cm (lowIdx t) i)) (dropLow t) := by
  rw [tl]; simp [ht]

theorem mw_zero (f E : ℕ) : mw cm f E 0 = E := by rw [mw]; simp

theorem mw_of_ne (f E : ℕ) {w : ℕ} (hw : w ≠ 0) :
    mw cm f E w = mw cm f (mg cm f E (lowIdx w)) (dropLow w) := by
  rw [mw]; simp [hw]

end Collector

structure PcData (g : ℕ → G) (cm : ℕ → ℕ → ℕ) (n : ℕ) : Prop where
  inv : ∀ k < n, g k * g k = 1
  rel : ∀ i j, i < j → j < n → g i * g j * g i = g j * nf g (cm j i)
  lt : ∀ i j, i < j → j < n → cm j i < 2 ^ n
  low : ∀ i j, i < j → j < n → LowZero (j + 1) (cm j i)

@[expose] def conjProd (g : ℕ → G) (cm : ℕ → ℕ → ℕ) (i t : ℕ) : G :=
  if _h : t = 0 then 1 else g (lowIdx t) * nf g (cm (lowIdx t) i) * conjProd g cm i (dropLow t)
termination_by t
decreasing_by exact dropLow_lt _h

theorem conjProd_zero (g : ℕ → G) (cm : ℕ → ℕ → ℕ) (i : ℕ) : conjProd g cm i 0 = 1 := by
  rw [conjProd]; simp

theorem conjProd_of_ne (g : ℕ → G) (cm : ℕ → ℕ → ℕ) (i : ℕ) {t : ℕ} (ht : t ≠ 0) :
    conjProd g cm i t = g (lowIdx t) * nf g (cm (lowIdx t) i) * conjProd g cm i (dropLow t) := by
  rw [conjProd]; simp [ht]

theorem lt_of_testBit {m n j : ℕ} (hm : m < 2 ^ n) (hj : m.testBit j = true) : j < n := by
  by_contra h
  rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega)
    (by omega : n ≤ j)))] at hj
  exact absurd hj (by decide)

theorem nf_split (g : ℕ → G) (E j : ℕ) :
    nf g E = nf g (E % 2 ^ j) * nf g (E &&& 2 ^ j) * nf g ((E >>> (j + 1)) <<< (j + 1)) := by
  have hT : LowZero (j + 1) ((E >>> (j + 1)) <<< (j + 1)) := fun k hk => by
    rw [Nat.testBit_shiftLeft]; simp; omega
  have hB : E &&& 2 ^ j < 2 ^ (j + 1) :=
    lt_of_le_of_lt Nat.and_le_right (Nat.pow_lt_pow_succ (by omega))
  have hBT : LowZero j ((E &&& 2 ^ j) ||| (E >>> (j + 1)) <<< (j + 1)) := fun k hk => by
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow, hT k (by omega)]; simp; omega
  conv_lhs => rw [eq_split E j]
  rw [nf_or g hBT _ (Nat.mod_lt _ (Nat.two_pow_pos j)), nf_or g hT _ hB, mul_assoc]

theorem nf_and_two_pow (g : ℕ → G) (E j : ℕ) :
    nf g (E &&& 2 ^ j) = if E.testBit j then g j else 1 := by
  rw [Nat.and_two_pow]
  cases E.testBit j <;> simp [nf_zero, nf_two_pow]

section Sound

variable {g : ℕ → G} {cm : ℕ → ℕ → ℕ} {n : ℕ}

@[expose] def GoodAt (g : ℕ → G) (cm : ℕ → ℕ → ℕ) (n f j : ℕ) : Prop :=
  ∀ E, E < 2 ^ n → nf g (mg cm f E j) = nf g E * g j ∧ mg cm f E j < 2 ^ n ∧
    ∀ k ≤ j, LowZero k E → LowZero k (mg cm f E j)

theorem conj_nf (hP : PcData g cm n) {i : ℕ} (hi : i < n) :
    ∀ t, LowZero (i + 1) t → t < 2 ^ n → g i * nf g t * g i = conjProd g cm i t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hlow ht
    by_cases h0 : t = 0
    · subst h0; rw [nf_zero, mul_one, conjProd_zero, hP.inv i hi]
    have hk := le_lowIdx_of_lowZero h0 hlow
    have hkn := lt_of_testBit ht (testBit_lowIdx h0)
    rw [nf_of_ne g h0, conjProd_of_ne g cm i h0, ← ih _ (dropLow_lt h0) (lowZero_dropLow hlow)
      (lt_two_pow_dropLow ht), ← hP.rel i _ (by omega) hkn]
    calc g i * (g (lowIdx t) * nf g (dropLow t)) * g i
        = g i * g (lowIdx t) * (g i * g i) * nf g (dropLow t) * g i := by
          rw [hP.inv i hi]; group
      _ = g i * g (lowIdx t) * g i * (g i * nf g (dropLow t) * g i) := by group

theorem mw_sound {f : ℕ} : ∀ w, (∀ j, w.testBit j = true → GoodAt g cm n f j) →
    ∀ E, E < 2 ^ n → nf g (mw cm f E w) = nf g E * nf g w ∧ mw cm f E w < 2 ^ n ∧
      ∀ k, LowZero k E → (∀ j, w.testBit j = true → k ≤ j) → LowZero k (mw cm f E w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw E hE
    by_cases h0 : w = 0
    · subst h0
      exact ⟨by rw [mw_zero, nf_zero, mul_one], by rw [mw_zero]; exact hE,
        fun k hk _ => by rw [mw_zero]; exact hk⟩
    obtain ⟨h1, h2, h3⟩ := hw _ (testBit_lowIdx h0) E hE
    have hsub : ∀ j, (dropLow w).testBit j = true → w.testBit j = true := fun j hj => by
      rw [testBit_dropLow h0] at hj; simp at hj; exact hj.1
    obtain ⟨i1, i2, i3⟩ := ih _ (dropLow_lt h0) (fun j hj => hw j (hsub j hj)) _ h2
    rw [mw_of_ne cm f E h0]
    refine ⟨by rw [i1, h1, nf_of_ne g h0, mul_assoc], i2, fun k hk hkw => ?_⟩
    exact i3 k (h3 k (hkw _ (testBit_lowIdx h0)) hk) fun j hj => hkw j (hsub j hj)

theorem tl_sound (hP : PcData g cm n) {f i : ℕ}
    (hgood : ∀ j, i < j → j < n → GoodAt g cm n f j) :
    ∀ t, t < 2 ^ n → LowZero (i + 1) t → ∀ r, r < 2 ^ n →
      nf g (tl cm f i r t) = nf g r * conjProd g cm i t ∧ tl cm f i r t < 2 ^ n ∧
        ∀ k ≤ i, LowZero k r → LowZero k (tl cm f i r t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht hlow r hr
    by_cases h0 : t = 0
    · subst h0
      exact ⟨by rw [tl_zero, conjProd_zero, mul_one], by rw [tl_zero]; exact hr,
        fun k _ h => by rw [tl_zero]; exact h⟩
    have hk := le_lowIdx_of_lowZero h0 hlow
    have hkn := lt_of_testBit ht (testBit_lowIdx h0)
    obtain ⟨a1, a2, a3⟩ := hgood _ hk hkn r hr
    have hcb : ∀ j, (cm (lowIdx t) i).testBit j = true → lowIdx t < j ∧ j < n := fun j hj => by
      refine ⟨?_, lt_of_testBit (hP.lt i _ (by omega) hkn) hj⟩
      by_contra hc
      rw [hP.low i _ (by omega) hkn j (by omega)] at hj
      exact absurd hj (by decide)
    obtain ⟨b1, b2, b3⟩ := mw_sound (cm (lowIdx t) i)
      (fun j hj => hgood j (by have := (hcb j hj).1; omega) (hcb j hj).2) _ a2
    obtain ⟨c1, c2, c3⟩ := ih _ (dropLow_lt h0) (lt_two_pow_dropLow ht) (lowZero_dropLow hlow) _ b2
    rw [tl_of_ne cm f i r h0]
    refine ⟨by rw [c1, b1, a1, conjProd_of_ne g cm i h0]; group, c2, fun k hk hr' => ?_⟩
    refine c3 k hk (b3 k (a3 k (by omega) hr') fun j hj => ?_)
    have := (hcb j hj).1
    omega

theorem goodAt (hP : PcData g cm n) : ∀ f j, j < n → n ≤ f + j → GoodAt g cm n f j := by
  intro f
  induction f with
  | zero => intro j hj h; omega
  | succ f ih =>
    intro j hj hf E hE
    have hgood : ∀ j', j < j' → j' < n → GoodAt g cm n f j' := fun j' h1 h2 =>
      ih j' h2 (by omega)
    set t := (E >>> (j + 1)) <<< (j + 1) with htdef
    set r := E % 2 ^ j ||| ((E ^^^ 2 ^ j) &&& 2 ^ j) with hrdef
    have htb : ∀ k, t.testBit k = (decide (k ≥ j + 1) && E.testBit k) := fun k => by
      rw [htdef, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      by_cases hk : k ≥ j + 1
      · have : j + 1 + (k - (j + 1)) = k := by omega
        simp [hk, this]
      · simp [hk]
    have ht : t < 2 ^ n := Nat.lt_pow_two_of_testBit _ fun k hk => by
      rw [htb, Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by omega) hk))]
      simp
    have htl : LowZero (j + 1) t := fun k hk => by rw [htb]; simp; omega
    have hrb : ∀ k, r.testBit k = if k < j then E.testBit k else
        if k = j then !E.testBit j else false := fun k => by
      rw [hrdef, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_xor,
        Nat.testBit_two_pow]
      by_cases h1 : k < j
      · have : j ≠ k := by omega
        simp [h1, this]
      · by_cases h2 : k = j
        · subst h2; simp
        · have : j ≠ k := by omega
          simp [h1, h2, this]
    have hr : r < 2 ^ n := Nat.lt_pow_two_of_testBit _ fun k hk => by
      rw [hrb]; have : ¬ k < j := by omega
      have : k ≠ j := by omega
      simp [*]
    obtain ⟨d1, d2, d3⟩ := tl_sound hP hgood t ht htl r hr
    rw [mg_succ]
    refine ⟨?_, d2, fun k hk hEk => d3 k hk fun j' hj' => ?_⟩
    · rw [d1, ← conj_nf hP hj t htl ht, nf_split g E j, nf_split g r j, nf_and_two_pow,
        nf_and_two_pow]
      have e1 : r % 2 ^ j = E % 2 ^ j := Nat.eq_of_testBit_eq fun k => by
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, hrb]
        by_cases h : k < j <;> simp [h]
      have e2 : (r >>> (j + 1)) <<< (j + 1) = 0 := Nat.eq_of_testBit_eq fun k => by
        rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, hrb, Nat.zero_testBit]
        have : ¬ j + 1 + (k - (j + 1)) < j := by omega
        have h' : j + 1 + (k - (j + 1)) ≠ j := by omega
        simp [this, h']
      rw [e1, e2, nf_zero, mul_one, hrb j, ← htdef]
      have key : g j * (g j * nf g t * g j) = nf g t * g j := by
        rw [← mul_assoc, ← mul_assoc, hP.inv j hj, one_mul]
      cases hEj : E.testBit j
      · simp only [lt_irrefl, ite_false, ite_true, Bool.not_false, Bool.false_eq_true,
          mul_one]
        rw [mul_assoc, key, ← mul_assoc]
      · simp only [lt_irrefl, ite_false, ite_true, Bool.not_true, Bool.false_eq_true, mul_one]
        group
    · rw [hrb]
      by_cases h1 : j' < j
      · simp [h1, hEk j' hj']
      · have : j' = j ∨ j < j' := by omega
        rcases this with h | h
        · omega
        · have : j' ≠ j := by omega
          simp [h1, this]

end Sound

@[expose] def mul (cm : ℕ → ℕ → ℕ) (n E F : ℕ) : ℕ := mw cm n E F

@[expose] def inv (cm : ℕ → ℕ → ℕ) (n E : ℕ) : ℕ :=
  if _h : E = 0 then 0 else mg cm n (inv cm n (dropLow E)) (lowIdx E)
termination_by E
decreasing_by exact dropLow_lt _h

@[expose] def mulList (cm : ℕ → ℕ → ℕ) (n E : ℕ) (l : List ℕ) : ℕ :=
  l.foldl (fun E k => mg cm n E k) E

section Products

variable {g : ℕ → G} {cm : ℕ → ℕ → ℕ} {n : ℕ} (hP : PcData g cm n)
include hP

theorem goodAt_n {j : ℕ} (hj : j < n) : GoodAt g cm n n j := goodAt hP n j hj (by omega)

theorem nf_mg {E j : ℕ} (hE : E < 2 ^ n) (hj : j < n) :
    nf g (mg cm n E j) = nf g E * g j ∧ mg cm n E j < 2 ^ n :=
  ⟨(goodAt_n hP hj E hE).1, (goodAt_n hP hj E hE).2.1⟩

theorem lowZero_mg {E j k : ℕ} (hE : E < 2 ^ n) (hj : j < n) (hk : k ≤ j) (h : LowZero k E) :
    LowZero k (mg cm n E j) := (goodAt_n hP hj E hE).2.2 k hk h

theorem nf_mul {E F : ℕ} (hE : E < 2 ^ n) (hF : F < 2 ^ n) :
    nf g (mul cm n E F) = nf g E * nf g F ∧ mul cm n E F < 2 ^ n :=
  have h := mw_sound F (fun _ hj => goodAt_n hP (lt_of_testBit hF hj)) E hE
  ⟨h.1, h.2.1⟩

theorem lowZero_mul {E F k : ℕ} (hE : E < 2 ^ n) (hF : F < 2 ^ n) (h1 : LowZero k E)
    (h2 : LowZero k F) : LowZero k (mul cm n E F) := by
  refine (mw_sound F (fun j hj => goodAt_n hP (lt_of_testBit hF hj)) E hE).2.2 k h1
    fun j hj => ?_
  by_contra hc
  rw [h2 j (by omega)] at hj
  exact absurd hj (by decide)

theorem nf_inv : ∀ E, E < 2 ^ n →
    nf g (inv cm n E) = (nf g E)⁻¹ ∧ inv cm n E < 2 ^ n ∧
      ∀ k, LowZero k E → LowZero k (inv cm n E) := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    by_cases h0 : E = 0
    · subst h0; rw [inv]
      exact ⟨by simp [nf_zero], by simp, fun _ _ => lowZero_zero _⟩
    obtain ⟨i1, i2, i3⟩ := ih _ (dropLow_lt h0) (lt_two_pow_dropLow hE)
    have hj := lt_of_testBit hE (testBit_lowIdx h0)
    obtain ⟨m1, m2⟩ := nf_mg hP i2 hj
    rw [inv]
    simp only [h0, dite_false]
    refine ⟨?_, m2, fun k hk => lowZero_mg hP i2 hj (le_lowIdx_of_lowZero h0 hk)
      (i3 k (lowZero_dropLow hk))⟩
    rw [m1, i1, nf_of_ne g h0, mul_inv_rev]
    congr 1
    exact (inv_eq_of_mul_eq_one_right (hP.inv _ hj)).symm

theorem nf_mulList : ∀ (l : List ℕ) (E : ℕ), (∀ k ∈ l, k < n) → E < 2 ^ n →
    nf g (mulList cm n E l) = nf g E * (l.map g).prod ∧ mulList cm n E l < 2 ^ n := by
  intro l
  induction l with
  | nil => intro E _ hE; simp [mulList, hE]
  | cons a l ih =>
    intro E hl hE
    obtain ⟨m1, m2⟩ := nf_mg hP hE (hl a (by simp))
    obtain ⟨r1, r2⟩ := ih (mg cm n E a) (fun k hk => hl k (by simp [hk])) m2
    refine ⟨?_, r2⟩
    change nf g (mulList cm n (mg cm n E a) l) = _
    rw [r1, m1, List.map_cons, List.prod_cons, mul_assoc]

end Products

@[expose] def gens (g : ℕ → G) (n : ℕ) : Subgroup G := Subgroup.closure {x | ∃ k < n, g k = x}

section Closure

variable {g : ℕ → G} {cm : ℕ → ℕ → ℕ} {n : ℕ} (hP : PcData g cm n)

theorem g_mem_gens {k : ℕ} (hk : k < n) : g k ∈ gens g n := Subgroup.subset_closure ⟨k, hk, rfl⟩

theorem nf_mem_gens : ∀ E, E < 2 ^ n → nf g E ∈ gens g n := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE
    by_cases h0 : E = 0
    · subst h0; rw [nf_zero]; exact one_mem _
    rw [nf_of_ne g h0]
    exact mul_mem (g_mem_gens (lt_of_testBit hE (testBit_lowIdx h0)))
      (ih _ (dropLow_lt h0) (lt_two_pow_dropLow hE))

include hP

theorem exists_nf_eq : ∀ x ∈ gens g n, ∃ E < 2 ^ n, nf g E = x := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨2 ^ k, Nat.pow_lt_pow_right (by omega) hk, nf_two_pow g k⟩
  | one => exact ⟨0, Nat.two_pow_pos n, nf_zero g⟩
  | mul x y _ _ hx hy =>
    obtain ⟨E, hE, rfl⟩ := hx
    obtain ⟨F, hF, rfl⟩ := hy
    exact ⟨mul cm n E F, (nf_mul hP hE hF).2, (nf_mul hP hE hF).1⟩
  | inv x _ hx =>
    obtain ⟨E, hE, rfl⟩ := hx
    exact ⟨inv cm n E, (nf_inv hP E hE).2.1, (nf_inv hP E hE).1⟩

theorem nf_injective (hcard : Nat.card (gens g n) = 2 ^ n) {E F : ℕ} (hE : E < 2 ^ n)
    (hF : F < 2 ^ n) (h : nf g E = nf g F) : E = F := by
  let f : Fin (2 ^ n) → gens g n := fun E => ⟨nf g E, nf_mem_gens E E.2⟩
  have hf : Function.Surjective f := fun x => by
    obtain ⟨E, hE, hx⟩ := exists_nf_eq hP x x.2
    exact ⟨⟨E, hE⟩, Subtype.ext hx⟩
  have hb := hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card,
    Fintype.card_fin])
  have := hb.1 (a₁ := ⟨E, hE⟩) (a₂ := ⟨F, hF⟩) (Subtype.ext h)
  exact congrArg Fin.val this

@[expose] def lowSub (k : ℕ) : Subgroup G where
  carrier := {x | ∃ E < 2 ^ n, LowZero k E ∧ nf g E = x}
  one_mem' := ⟨0, Nat.two_pow_pos n, lowZero_zero k, nf_zero g⟩
  mul_mem' := by
    rintro _ _ ⟨E, hE, hEk, rfl⟩ ⟨F, hF, hFk, rfl⟩
    exact ⟨mul cm n E F, (nf_mul hP hE hF).2, lowZero_mul hP hE hF hEk hFk, (nf_mul hP hE hF).1⟩
  inv_mem' := by
    rintro _ ⟨E, hE, hEk, rfl⟩
    exact ⟨inv cm n E, (nf_inv hP E hE).2.1, (nf_inv hP E hE).2.2 k hEk, (nf_inv hP E hE).1⟩

theorem nf_mem_lowSub {k E : ℕ} (hE : E < 2 ^ n) (hk : LowZero k E) :
    nf g E ∈ lowSub hP k := ⟨E, hE, hk, rfl⟩

theorem mem_lowSub_iff (hcard : Nat.card (gens g n) = 2 ^ n) {k E : ℕ} (hE : E < 2 ^ n) :
    nf g E ∈ lowSub hP k ↔ LowZero k E := by
  refine ⟨fun ⟨F, hF, hFk, h⟩ => ?_, nf_mem_lowSub hP hE⟩
  rw [nf_injective hP hcard hF hE h] at hFk
  exact hFk

theorem lowSub_anti {k k' : ℕ} (h : k ≤ k') : lowSub hP k' ≤ lowSub hP k := by
  rintro _ ⟨E, hE, hk, rfl⟩
  exact ⟨E, hE, lowZero_of_le hk h, rfl⟩

theorem g_mem_lowSub {k i : ℕ} (hki : k ≤ i) (hi : i < n) : g i ∈ lowSub hP k := by
  rw [← nf_two_pow g i]
  refine nf_mem_lowSub hP (Nat.pow_lt_pow_right (by omega) hi) fun j hj => ?_
  rw [Nat.testBit_two_pow]; simp; omega

end Closure

section Normal

variable {g : ℕ → G} {cm : ℕ → ℕ → ℕ} {n : ℕ} (hP : PcData g cm n)
include hP

theorem g_inv {k : ℕ} (hk : k < n) : (g k)⁻¹ = g k := inv_eq_of_mul_eq_one_right (hP.inv k hk)

theorem conjProd_mem {i k : ℕ} (hik : i < k) :
    ∀ E, E < 2 ^ n → LowZero k E → conjProd g cm i E ∈ lowSub hP k := by
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro hE hk
    by_cases h0 : E = 0
    · subst h0; rw [conjProd_zero]; exact one_mem _
    have hm := le_lowIdx_of_lowZero h0 hk
    have hmn := lt_of_testBit hE (testBit_lowIdx h0)
    rw [conjProd_of_ne g cm i h0]
    refine mul_mem (mul_mem (g_mem_lowSub hP hm hmn) (nf_mem_lowSub hP (hP.lt i _ (by omega) hmn)
      (lowZero_of_le (hP.low i _ (by omega) hmn) (by omega)))) ?_
    exact ih _ (dropLow_lt h0) (lt_two_pow_dropLow hE) (lowZero_dropLow hk)

theorem conj_gen_mem {i k : ℕ} (hi : i < n) {y : G} (hy : y ∈ lowSub hP k) :
    g i * y * (g i)⁻¹ ∈ lowSub hP k := by
  by_cases hik : k ≤ i
  · exact mul_mem (mul_mem (g_mem_lowSub hP hik hi) hy) (inv_mem (g_mem_lowSub hP hik hi))
  obtain ⟨E, hE, hEk, rfl⟩ := hy
  rw [g_inv hP hi, conj_nf hP hi E (lowZero_of_le hEk (by omega)) hE]
  exact conjProd_mem hP (by omega) E hE hEk

theorem conj_mem {k : ℕ} {x : G} (hx : x ∈ gens g n) :
    ∀ y ∈ lowSub hP k, x * y * x⁻¹ ∈ lowSub hP k := by
  induction hx using Subgroup.closure_induction_left with
  | one => intro y hy; simpa using hy
  | mul_left x hx x' _ h' =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro y hy
    rw [show g i * x' * y * (g i * x')⁻¹ = g i * (x' * y * x'⁻¹) * (g i)⁻¹ by group]
    exact conj_gen_mem hP hi (h' y hy)
  | inv_mul_cancel x hx x' _ h' =>
    obtain ⟨i, hi, rfl⟩ := hx
    intro y hy
    rw [g_inv hP hi, show g i * x' * y * (g i * x')⁻¹ = g i * (x' * y * x'⁻¹) * (g i)⁻¹ by group]
    exact conj_gen_mem hP hi (h' y hy)

theorem commutator_gen_mem {k : ℕ} (hk : k < n) {s : G} (hs : s ∈ gens g n) :
    ⁅g k, s⁆ ∈ lowSub hP (k + 1) := by
  have hgen : ∀ i < n, ⁅g k, g i⁆ ∈ lowSub hP (k + 1) := by
    intro i hi
    rw [commutatorElement_def, g_inv hP hk, g_inv hP hi]
    rcases lt_trichotomy i k with h | h | h
    · have e : g k * g i * g k * g i = nf g (cm k i) :=
        calc g k * g i * g k * g i = g k * (g i * g k * g i) := by group
          _ = g k * (g k * nf g (cm k i)) := by rw [hP.rel i k h hk]
          _ = nf g (cm k i) := by rw [← mul_assoc, hP.inv k hk, one_mul]
      rw [e]
      exact nf_mem_lowSub hP (hP.lt i k h hk) (hP.low i k h hk)
    · subst h; rw [hP.inv i hi, one_mul, hP.inv i hi]; exact one_mem _
    · have e : g k * g i * g k * g i = g i * nf g (cm i k) * (g i)⁻¹ := by
        rw [hP.rel k i h hi, g_inv hP hi]
      rw [e]
      exact conj_gen_mem hP hi (lowSub_anti hP (by omega : k + 1 ≤ i + 1)
        (nf_mem_lowSub hP (hP.lt k i h hi) (hP.low k i h hi)))
  have hmul : ∀ i < n, ∀ x', ⁅g k, x'⁆ ∈ lowSub hP (k + 1) →
      ⁅g k, g i * x'⁆ ∈ lowSub hP (k + 1) := fun i hi x' h' => by
    rw [show ⁅g k, g i * x'⁆ = ⁅g k, g i⁆ * (g i * ⁅g k, x'⁆ * (g i)⁻¹) by
      simp only [commutatorElement_def]; group]
    exact mul_mem (hgen i hi) (conj_gen_mem hP hi h')
  induction hs using Subgroup.closure_induction_left with
  | one => rw [commutatorElement_one_right]; exact one_mem _
  | mul_left x hx x' _ h' => obtain ⟨i, hi, rfl⟩ := hx; exact hmul i hi x' h'
  | inv_mul_cancel x hx x' _ h' =>
    obtain ⟨i, hi, rfl⟩ := hx; rw [g_inv hP hi]; exact hmul i hi x' h'

theorem commutator_mem_succ {k : ℕ} {q s : G} (hq : q ∈ lowSub hP k) (hs : s ∈ gens g n) :
    ⁅q, s⁆ ∈ lowSub hP (k + 1) := by
  obtain ⟨E, hE, hEk, rfl⟩ := hq
  by_cases hb : E.testBit k = true
  · have h0 : E ≠ 0 := fun h => by rw [h, Nat.zero_testBit] at hb; exact absurd hb (by decide)
    have hlow : lowIdx E = k := lowIdx_eq hb hEk
    have hkn := lt_of_testBit hE hb
    have hq' : nf g (dropLow E) ∈ lowSub hP (k + 1) := by
      refine nf_mem_lowSub hP (lt_two_pow_dropLow hE) fun j hj => ?_
      rw [testBit_dropLow h0, hlow]
      by_cases hjk : j = k
      · simp [hjk]
      · simp [hEk j (by omega)]
    rw [nf_of_ne g h0, hlow, show ⁅g k * nf g (dropLow E), s⁆ =
      g k * ⁅nf g (dropLow E), s⁆ * (g k)⁻¹ * ⁅g k, s⁆ by simp only [commutatorElement_def]; group]
    refine mul_mem (conj_gen_mem hP hkn ?_) (commutator_gen_mem hP hkn hs)
    rw [show ⁅nf g (dropLow E), s⁆ = nf g (dropLow E) * (s * (nf g (dropLow E))⁻¹ * s⁻¹) by
      simp only [commutatorElement_def]; group]
    exact mul_mem hq' (conj_mem hP hs _ (inv_mem hq'))
  · have hE' : nf g E ∈ lowSub hP (k + 1) := nf_mem_lowSub hP hE fun j hj => by
      by_cases hjk : j = k
      · subst hjk; simpa using hb
      · exact hEk j (by omega)
    rw [show ⁅nf g E, s⁆ = nf g E * (s * (nf g E)⁻¹ * s⁻¹) by
      simp only [commutatorElement_def]; group]
    exact mul_mem hE' (conj_mem hP hs _ (inv_mem hE'))

theorem commutator_mul_mem_iff {k : ℕ} {p q s : G} (hp : p ∈ gens g n) (hq : q ∈ lowSub hP k)
    (hs : s ∈ gens g n) : ⁅p * q, s⁆ ∈ lowSub hP (k + 1) ↔ ⁅p, s⁆ ∈ lowSub hP (k + 1) := by
  rw [show ⁅p * q, s⁆ = p * ⁅q, s⁆ * p⁻¹ * ⁅p, s⁆ by simp only [commutatorElement_def]; group]
  exact Subgroup.mul_mem_cancel_left _ (conj_mem hP hp _ (commutator_mem_succ hP hq hs))

theorem sq_mul_mem_iff {k : ℕ} {x y : G} (hx : x ∈ gens g n) (hy : y ∈ lowSub hP k) :
    x * y * (x * y) ∈ lowSub hP k ↔ x * x ∈ lowSub hP k := by
  rw [show x * y * (x * y) = x * x * (x⁻¹ * y * x⁻¹⁻¹ * y) by group]
  exact Subgroup.mul_mem_cancel_right _ (mul_mem (conj_mem hP (inv_mem hx) _ hy) hy)

end Normal

theorem lowZero_iff_mod (k m : ℕ) : LowZero k m ↔ m % 2 ^ k = 0 := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hj : j < k
    · simp [hj, h j hj]
    · simp [hj]
  · intro h j hj
    have := congrArg (fun m => m.testBit j) h
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit] at this
    simpa [hj] using this

theorem nf_mod_high (g : ℕ → G) (E k : ℕ) :
    nf g E = nf g (E % 2 ^ k) * nf g ((E >>> k) <<< k) := by
  have hT : LowZero k ((E >>> k) <<< k) := fun j hj => by
    rw [Nat.testBit_shiftLeft]; simp; omega
  conv_lhs => rw [show E = E % 2 ^ k ||| (E >>> k) <<< k from Nat.eq_of_testBit_eq fun j => by
    rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    by_cases hj : j < k
    · simp [hj]
    · have : k + (j - k) = j := by omega
      simp [hj, this]; omega]
  exact nf_or g hT _ (Nat.mod_lt _ (Nat.two_pow_pos k))

theorem nf_mod_succ (g : ℕ → G) (E k : ℕ) :
    nf g (E % 2 ^ (k + 1)) = nf g (E % 2 ^ k) * nf g (E &&& 2 ^ k) := by
  have hT : LowZero k (E &&& 2 ^ k) := fun j hj => by
    rw [Nat.testBit_and, Nat.testBit_two_pow]; simp; omega
  conv_lhs => rw [show E % 2 ^ (k + 1) = E % 2 ^ k ||| (E &&& 2 ^ k) from
    Nat.eq_of_testBit_eq fun j => by
      rw [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_and,
        Nat.testBit_two_pow]
      by_cases hj : j < k
      · have : j < k + 1 := by omega
        have : k ≠ j := by omega
        simp [*]
      · by_cases hjk : j = k
        · subst hjk; simp
        · have : ¬ j < k + 1 := by omega
          have : k ≠ j := by omega
          simp [*]]
  exact nf_or g hT _ (Nat.mod_lt _ (Nat.two_pow_pos k))

theorem mod_succ_eq (E k : ℕ) :
    E % 2 ^ (k + 1) = E % 2 ^ k ∨ E % 2 ^ (k + 1) = E % 2 ^ k + 2 ^ k := by
  have h2 : E % (2 ^ k * 2) = E % 2 ^ k + 2 ^ k * (E / 2 ^ k % 2) := Nat.mod_mul
  rw [pow_succ, h2]
  rcases Nat.mod_two_eq_zero_or_one (E / 2 ^ k) with h | h <;> simp [h]

@[expose] def extend (k : ℕ) (cur : Array ℕ) : Array ℕ := cur.flatMap fun p => #[p, p + 2 ^ k]

theorem mem_extend {k p : ℕ} {cur : Array ℕ} (hp : p % 2 ^ k ∈ cur) :
    p % 2 ^ (k + 1) ∈ extend k cur := by
  rw [extend, Array.mem_flatMap]
  refine ⟨_, hp, ?_⟩
  rcases mod_succ_eq p k with h | h <;> rw [h] <;> simp

section Search

variable (cm : ℕ → ℕ → ℕ) (n : ℕ)

@[expose] def preSq : ℕ → Array ℕ
  | 0 => #[0]
  | k + 1 => (extend k (preSq k)).filter fun q => mul cm n q q % 2 ^ (k + 1) == 0

@[expose] def commGen (E i : ℕ) : ℕ := mg cm n (mul cm n (mg cm n E i) (inv cm n E)) i

@[expose] def preCen : ℕ → Array ℕ
  | 0 => #[0]
  | k + 1 => (extend k (preCen k)).filter fun q =>
      (List.range n).all fun i => commGen cm n q i % 2 ^ (k + 2) == 0

end Search

theorem lt_of_mem_extend {k : ℕ} {cur : Array ℕ} (h : ∀ p ∈ cur, p < 2 ^ k) :
    ∀ q ∈ extend k cur, q < 2 ^ (k + 1) := by
  intro q hq
  rw [extend, Array.mem_flatMap] at hq
  obtain ⟨p, hp, hq⟩ := hq
  have := h p hp
  rw [pow_succ]
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl <;> omega

theorem nodup_extend {k : ℕ} {cur : Array ℕ} (h : ∀ p ∈ cur, p < 2 ^ k) (hn : cur.toList.Nodup) :
    (extend k cur).toList.Nodup := by
  rw [extend, Array.toList_flatMap]
  refine List.nodup_flatMap.2 ⟨fun p hp => ?_, ?_⟩
  · have := h p (Array.mem_toList_iff.1 hp)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true, not_false_eq_true]
    have : 0 < 2 ^ k := Nat.two_pow_pos k
    omega
  · refine hn.pairwise_of_forall_ne fun a ha b hb hab => ?_
    rw [Function.onFun, List.disjoint_iff_ne]
    have ha' := h a (Array.mem_toList_iff.1 ha)
    have hb' := h b (Array.mem_toList_iff.1 hb)
    intro x hx y hy hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> omega

theorem preSq_spec (cm : ℕ → ℕ → ℕ) (n : ℕ) :
    ∀ k, (∀ p ∈ preSq cm n k, p < 2 ^ k) ∧ (preSq cm n k).toList.Nodup := by
  intro k
  induction k with
  | zero => simp [preSq]
  | succ k ih =>
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [preSq, Array.mem_filter] at hp
      exact lt_of_mem_extend ih.1 p hp.1
    · rw [preSq, Array.toList_filter]
      exact (nodup_extend ih.1 ih.2).filter _

theorem nf_eq_prod (g : ℕ → G) : ∀ n E, E < 2 ^ n →
    nf g E = (((List.range n).filter fun k => E.testBit k).map g).prod := by
  intro n
  induction n with
  | zero => intro E hE; simp at hE; subst hE; simp [nf_zero]
  | succ n ih =>
    intro E hE
    have hE' : E % 2 ^ (n + 1) = E := Nat.mod_eq_of_lt hE
    have h1 := nf_mod_succ g E n
    rw [hE'] at h1
    rw [h1, ih _ (Nat.mod_lt _ (Nat.two_pow_pos n)), nf_and_two_pow, List.range_succ,
      List.filter_append, List.map_append, List.prod_append]
    have hf : (List.range n).filter (fun k => (E % 2 ^ n).testBit k) =
        (List.range n).filter (fun k => E.testBit k) := by
      refine List.filter_congr fun k hk => ?_
      rw [List.mem_range] at hk
      rw [Nat.testBit_mod_two_pow]; simp [hk]
    rw [hf]
    cases h : E.testBit n <;> simp [h]

section SearchSound

variable {g : ℕ → G} {cm : ℕ → ℕ → ℕ} {n : ℕ} (hP : PcData g cm n)
  (hcard : Nat.card (gens g n) = 2 ^ n)
include hP hcard

omit hP hcard in
theorem mod_lt_two_pow {E : ℕ} (hE : E < 2 ^ n) (k : ℕ) : E % 2 ^ k < 2 ^ n :=
  lt_of_le_of_lt (Nat.mod_le _ _) hE

theorem mem_preSq {E : ℕ} (hE : E < 2 ^ n) : ∀ k,
    nf g (E % 2 ^ k) * nf g (E % 2 ^ k) ∈ lowSub hP k → E % 2 ^ k ∈ preSq cm n k := by
  intro k
  induction k with
  | zero => intro _; simp [preSq, Nat.mod_one]
  | succ k ih =>
    intro h
    have hy : nf g (E &&& 2 ^ k) ∈ lowSub hP k :=
      nf_mem_lowSub hP (lt_of_le_of_lt Nat.and_le_left hE) fun j hj => by
        rw [Nat.testBit_and, Nat.testBit_two_pow]; simp; omega
    have hx := nf_mem_gens (g := g) _ (mod_lt_two_pow hE k)
    rw [nf_mod_succ] at h
    have h' := (sq_mul_mem_iff hP hx hy).1 (lowSub_anti hP (Nat.le_succ k) h)
    rw [preSq, Array.mem_filter]
    refine ⟨mem_extend (ih h'), ?_⟩
    have hm := nf_mul hP (mod_lt_two_pow hE (k + 1)) (mod_lt_two_pow hE (k + 1))
    have hmem : nf g (mul cm n (E % 2 ^ (k + 1)) (E % 2 ^ (k + 1))) ∈ lowSub hP (k + 1) := by
      rw [hm.1, nf_mod_succ]; exact h
    rw [mem_lowSub_iff hP hcard hm.2, lowZero_iff_mod] at hmem
    simp [hmem]

omit hcard in
theorem nf_commGen {E i : ℕ} (hE : E < 2 ^ n) (hi : i < n) :
    nf g (commGen cm n E i) = ⁅nf g E, g i⁆ ∧ commGen cm n E i < 2 ^ n := by
  obtain ⟨a1, a2⟩ := nf_mg hP hE hi
  obtain ⟨b1, b2, -⟩ := nf_inv hP E hE
  obtain ⟨c1, c2⟩ := nf_mul hP a2 b2
  obtain ⟨d1, d2⟩ := nf_mg hP c2 hi
  refine ⟨?_, d2⟩
  rw [commGen, d1, c1, a1, b1, commutatorElement_def, g_inv hP hi]

theorem mem_preCen {E : ℕ} (hE : E < 2 ^ n) (hc : ∀ i < n, ⁅nf g E, g i⁆ = 1) :
    ∀ k, E % 2 ^ k ∈ preCen cm n k := by
  have key : ∀ k, ∀ i < n, ⁅nf g (E % 2 ^ k), g i⁆ ∈ lowSub hP (k + 1) := fun k i hi => by
    have hq : nf g ((E >>> k) <<< k) ∈ lowSub hP k := by
      refine nf_mem_lowSub hP ?_ fun j hj => by rw [Nat.testBit_shiftLeft]; simp; omega
      refine Nat.lt_pow_two_of_testBit _ fun j hj => ?_
      rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
      by_cases hjk : j ≥ k
      · have : k + (j - k) = j := by omega
        simp only [hjk, decide_true, Bool.true_and, this]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by omega) hj))
      · simp [hjk]
    have h := hc i hi
    rw [nf_mod_high g E k] at h
    exact (commutator_mul_mem_iff hP (nf_mem_gens _ (mod_lt_two_pow hE k)) hq
      (g_mem_gens hi)).1 (h ▸ one_mem _)
  intro k
  induction k with
  | zero => simp [preCen, Nat.mod_one]
  | succ k ih =>
    rw [preCen, Array.mem_filter]
    refine ⟨mem_extend ih, ?_⟩
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro i hi
    obtain ⟨h1, h2⟩ := nf_commGen hP (mod_lt_two_pow hE (k + 1)) hi
    have hmem := key (k + 1) i hi
    rw [← h1, mem_lowSub_iff hP hcard h2, lowZero_iff_mod] at hmem
    exact hmem

end SearchSound

end CFSG.EvenSmallLie.FFourTwo.Pc
