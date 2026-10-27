module

public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

@[expose] def prev (θ : Fin n → ℤ) (i : Fin n) : ℤ :=
  if h : 0 < i.val then θ ⟨i.val - 1, by omega⟩ else 0

@[expose] def next (θ : Fin n → ℤ) (i : Fin n) : ℤ :=
  if h : i.val + 1 < n then θ ⟨i.val + 1, h⟩ else 0

theorem sum_prev_eq (f : Fin n → ℤ) (i : Fin n) :
    ∑ j : Fin n, (if j.val + 1 = i.val then f j else 0) = prev f i := by
  unfold prev
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin n)]
    · simp [show (i.val - 1) + 1 = i.val by omega]
    · intro j _ hj
      have hc : ¬ (j.val + 1 = i.val) := by
        intro hc
        apply hj
        ext
        simp only
        omega
      simp [hc]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have hc : ¬ (j.val + 1 = i.val) := by omega
    simp [hc]

theorem sum_next_eq (f : Fin n → ℤ) (i : Fin n) :
    ∑ j : Fin n, (if i.val + 1 = j.val then f j else 0) = next f i := by
  unfold next
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i.val + 1, h⟩ : Fin n)]
    · simp
    · intro j _ hj
      have hc : ¬ (i.val + 1 = j.val) := by
        intro hc
        apply hj
        ext
        simp only
        omega
      simp [hc]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have := j.isLt
    have hc : ¬ (i.val + 1 = j.val) := by omega
    simp [hc]

theorem tri_row (a b : Fin n → ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (θ : Fin n → ℤ) (i : Fin n)
    (hM : ∀ j, M i j = if i = j then 2 else if j.val + 1 = i.val then -a i else
      if i.val + 1 = j.val then -b i else 0) :
    ∑ j, M i j * θ j = 2 * θ i - a i * prev θ i - b i * next θ i := by
  have h1 : ∀ j : Fin n, M i j * θ j = (if i = j then 2 * θ j else 0) +
      (-a i) * (if j.val + 1 = i.val then θ j else 0) +
      (-b i) * (if i.val + 1 = j.val then θ j else 0) := by
    intro j
    rw [hM j]
    by_cases hij : i = j
    · subst hij; simp
    · have h' : i.val ≠ j.val := fun e => hij (Fin.ext e)
      by_cases hp : j.val + 1 = i.val
      · have hq : ¬ i.val + 1 = j.val := by omega
        simp [hij, hp, hq]
      · by_cases hq : i.val + 1 = j.val
        · simp [hij, hp, hq]
        · simp [hij, hp, hq]
  simp only [h1]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_prev_eq, sum_next_eq]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  ring

theorem closed_form (T : ℕ → ℤ) (β N : ℕ)
    (hrow : ∀ i, i ≤ N →
      2 * T i - (if i = 0 then 0 else T (i - 1)) - T (i + 1) = if i = β then 1 else 0) :
    ∀ k, k ≤ N + 1 → T k = ((k : ℤ) + 1) * T 0 - max ((k : ℤ) - β) 0 := by
  have key : ∀ k, k ≤ N → (T k = ((k : ℤ) + 1) * T 0 - max ((k : ℤ) - β) 0 ∧
      T (k + 1) = ((k : ℤ) + 2) * T 0 - max ((k : ℤ) + 1 - β) 0) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have h0 := hrow 0 (by omega)
      simp only [↓reduceIte, sub_zero, zero_add] at h0
      refine ⟨by simp, ?_⟩
      norm_num
      omega
    | succ k ih =>
      intro hk
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have h1 := hrow (k + 1) hk
      simp only [Nat.add_sub_cancel, show k + 1 ≠ 0 from Nat.succ_ne_zero k, ↓reduceIte] at h1
      refine ⟨by push_cast; linarith, ?_⟩
      push_cast
      have hm : 2 * max ((k : ℤ) + 1 - β) 0 - max ((k : ℤ) - β) 0 + (if k + 1 = β then 1 else 0) =
          max ((k : ℤ) + 1 + 1 - β) 0 := by
        split_ifs <;> omega
      have e3 : T (k + 1 + 1) = 2 * T (k + 1) - T k - (if k + 1 = β then 1 else 0) := by omega
      rw [e3, ih1, ih2]
      linarith [hm]
  intro k hk
  by_cases hk' : k ≤ N
  · exact (key k hk').1
  · have : k = N + 1 := by omega
    subst this
    have := (key N le_rfl).2
    push_cast
    linarith

@[expose] def extN (θ : Fin n → ℤ) : ℕ → ℤ := fun k => if h : k < n then θ ⟨k, h⟩ else 0

theorem extN_of_lt (θ : Fin n → ℤ) (i : Fin n) : extN θ i.val = θ i := by
  simp [extN]

theorem extN_of_ge (θ : Fin n → ℤ) {k : ℕ} (hk : n ≤ k) : extN θ k = 0 := by
  simp [extN, show ¬ k < n by omega]

theorem prev_eq (θ : Fin n → ℤ) (i : Fin n) :
    prev θ i = if i.val = 0 then 0 else extN θ (i.val - 1) := by
  unfold prev extN
  by_cases h : i.val = 0
  · simp [h]
  · have h' : 0 < i.val := Nat.pos_of_ne_zero h
    simp only [h', dite_true, h, ↓reduceIte, show i.val - 1 < n by omega]

theorem next_eq (θ : Fin n → ℤ) (i : Fin n) : next θ i = extN θ (i.val + 1) := rfl

theorem tri_rec_unit (M : Matrix (Fin n) (Fin n) ℤ) (θ : Fin n → ℤ) (β : ℕ)
    (hM : ∀ i j, M i j = if i = j then 2 else if j.val + 1 = i.val then -1 else
      if i.val + 1 = j.val then -1 else 0)
    (hθ : ∀ i : Fin n, ∑ j, M i j * θ j = if i.val = β then 1 else 0) (i : ℕ) (hi : i < n) :
    2 * extN θ i - (if i = 0 then 0 else extN θ (i - 1)) - extN θ (i + 1) =
      if i = β then 1 else 0 := by
  have h := hθ ⟨i, hi⟩
  rw [tri_row (fun _ => 1) (fun _ => 1) M θ ⟨i, hi⟩ (hM ⟨i, hi⟩), prev_eq, next_eq] at h
  simpa [extN_of_lt, hi, extN] using h

theorem not_ext_A {β : Fin n} {θ : Fin n → ℤ}
    (hθ : ∀ i, ∑ j, CartanMatrix.A n i j * θ j = if i = β then 1 else 0) : False := by
  have hM : ∀ i j : Fin n, CartanMatrix.A n i j = if i = j then 2 else if j.val + 1 = i.val
      then -1 else if i.val + 1 = j.val then -1 else 0 := by
    intro i j
    unfold CartanMatrix.A
    simp only [Matrix.of_apply]
    split_ifs <;> first | rfl | omega
  have hrow := tri_rec_unit (CartanMatrix.A n) θ β.val hM
    (fun i => by rw [hθ i]; simp [Fin.ext_iff])
  have hn : 0 < n := β.pos
  have hcl := closed_form (extN θ) β.val (n - 1) (fun i hi => hrow i (by omega)) n (by omega)
  rw [extN_of_ge θ le_rfl] at hcl
  have hβ := β.isLt
  have h0 : (0 : ℤ) = ((n : ℤ) + 1) * extN θ 0 - ((n : ℤ) - β.val) := by
    rw [hcl]; omega
  rcases le_or_gt (extN θ 0) 0 with h | h
  · nlinarith
  · nlinarith

theorem tri_rec (a b : Fin n → ℤ) (M : Matrix (Fin n) (Fin n) ℤ) (θ : Fin n → ℤ) (β : ℕ)
    (hM : ∀ i j, M i j = if i = j then 2 else if j.val + 1 = i.val then -a i else
      if i.val + 1 = j.val then -b i else 0)
    (hθ : ∀ i : Fin n, ∑ j, M i j * θ j = if i.val = β then 1 else 0) (i : ℕ) (hi : i < n) :
    2 * extN θ i - a ⟨i, hi⟩ * (if i = 0 then 0 else extN θ (i - 1)) -
        b ⟨i, hi⟩ * extN θ (i + 1) = if i = β then 1 else 0 := by
  have h := hθ ⟨i, hi⟩
  rw [tri_row a b M θ ⟨i, hi⟩ (hM ⟨i, hi⟩), prev_eq, next_eq] at h
  simpa [extN_of_lt, hi, extN] using h

theorem stdCartan_B_tri (i j : Fin n) : stdCartan (.B n) i j =
    if i = j then 2 else if j.val + 1 = i.val then -(if i.val + 1 = n then 2 else 1) else
      if i.val + 1 = j.val then -1 else 0 := by
  rw [stdCartan_B n i j]
  unfold CartanMatrix.B
  simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i = j
  · subst hij; simp
  · have h' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have h'' : j ≠ i := fun e => hij e.symm
    simp only [hij, h'', ite_false]
    split_ifs <;> omega

theorem stdCartan_C_tri (i j : Fin n) : stdCartan (.C n) i j =
    if i = j then 2 else if j.val + 1 = i.val then -1 else
      if i.val + 1 = j.val then -(if i.val + 2 = n then 2 else 1) else 0 := by
  rw [stdCartan_C n i j]
  unfold CartanMatrix.C
  simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i = j
  · subst hij; simp
  · have h' : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have h'' : j ≠ i := fun e => hij e.symm
    simp only [hij, h'', ite_false]
    split_ifs <;> omega

theorem ext_B (hn : 2 ≤ n) {β : Fin n} {θ : Fin n → ℤ}
    (hθ : ∀ i : Fin n, ∑ j, stdCartan (.B n) i j * θ j = if i = β then 1 else 0)
    (hθβ : θ β = 2) : 3 ≤ n ∧ β.val = 1 := by
  have hrow := tri_rec (n := n) (fun i => if i.val + 1 = n then 2 else 1) (fun _ => 1) (stdCartan (.B n)) θ
    β.val (fun (i j : Fin n) => stdCartan_B_tri i j)
    (fun (i : Fin n) => (hθ i).trans (by simp [Fin.ext_iff]))
  have hβ := β.isLt
  have hcl := closed_form (extN θ) β.val (n - 2) (fun i hi => by
    have := hrow i (by omega)
    simpa [show i + 1 ≠ n by omega] using this)
  have hlast := hrow (n - 1) (by omega)
  have e1 : n - 1 + 1 = n := by omega
  have e2 : n - 1 ≠ 0 := by omega
  have e3 : n - 1 - 1 = n - 2 := by omega
  have e4 : extN θ (n - 1 + 1) = 0 := extN_of_ge θ (by omega)
  simp only [e1, e2, e3, ↓reduceIte] at hlast
  rw [e1] at e4
  rw [e4] at hlast
  have f1 := hcl (n - 1) (by omega)
  have f2 := hcl (n - 2) (by omega)
  have hprod : (((n - 1 : ℕ) : ℤ) + 1) * extN θ 0 =
      (((n - 2 : ℕ) : ℤ) + 1) * extN θ 0 + extN θ 0 := by
    have : ((n - 1 : ℕ) : ℤ) = ((n - 2 : ℕ) : ℤ) + 1 := by omega
    rw [this]; ring
  have hb1 : β.val ≠ n - 1 := by
    intro h
    simp only [h, ↓reduceIte] at hlast
    omega
  have hT0 : extN θ 0 = 1 := by
    have : ¬ (n - 1 = β.val) := fun h => hb1 h.symm
    simp only [this, ↓reduceIte] at hlast
    omega
  have hk := hcl β.val (by omega)
  rw [extN_of_lt, hθβ, hT0] at hk
  refine ⟨by omega, by omega⟩

theorem ext_C (hn : 3 ≤ n) {β : Fin n} {θ : Fin n → ℤ}
    (hθ : ∀ i : Fin n, ∑ j, stdCartan (.C n) i j * θ j = if i = β then 1 else 0)
    (hθβ : θ β = 2) (hβ : β.val + 1 = n) : n = 4 := by
  have hrow := tri_rec (n := n) (fun _ => 1) (fun i => if i.val + 2 = n then 2 else 1)
    (stdCartan (.C n)) θ β.val (fun (i j : Fin n) => stdCartan_C_tri i j)
    (fun (i : Fin n) => (hθ i).trans (by simp [Fin.ext_iff]))
  have hcl := closed_form (extN θ) β.val (n - 3) (fun i hi => by
    have := hrow i (by omega)
    simpa [show i + 2 ≠ n by omega] using this)
  have r1 := hrow (n - 2) (by omega)
  have r2 := hrow (n - 1) (by omega)
  have e1 : n - 2 + 2 = n := by omega
  have e2 : n - 2 ≠ 0 := by omega
  have e3 : n - 2 - 1 = n - 3 := by omega
  have e4 : n - 2 + 1 = n - 1 := by omega
  have e5 : n - 1 + 1 = n := by omega
  have e6 : n - 1 ≠ 0 := by omega
  have e7 : n - 1 - 1 = n - 2 := by omega
  have e8 : extN θ n = 0 := extN_of_ge θ le_rfl
  simp only [e1, e2, e3, e4, ↓reduceIte] at r1
  simp only [e5, e6, e7, e8, ↓reduceIte, show n - 1 + 2 ≠ n by omega] at r2
  have f2 := hcl (n - 2) (by omega)
  have f3 := hcl (n - 3) (by omega)
  have hprod : (((n - 2 : ℕ) : ℤ) + 1) * extN θ 0 =
      (((n - 3 : ℕ) : ℤ) + 1) * extN θ 0 + extN θ 0 := by
    have : ((n - 2 : ℕ) : ℤ) = ((n - 3 : ℕ) : ℤ) + 1 := by omega
    rw [this]; ring
  have hβ' : β.val = n - 1 := by omega
  have hc : extN θ 0 = 1 := by
    simp only [hβ', ↓reduceIte] at r1 r2 f2 f3
    omega
  have hk := hcl (n - 2) (by omega)
  rw [hc] at hk
  have hw : extN θ (n - 1) = 2 := by
    rw [← hθβ]
    have : (β : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hβ'
    rw [this]
    exact extN_of_lt θ ⟨n - 1, by omega⟩
  simp only [hβ', ↓reduceIte] at r1 r2 f2 f3
  rw [hc] at f2 f3
  omega

end CFSG.ClassicalInvolution.RouteD
