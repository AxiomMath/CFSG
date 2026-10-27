module

public import CFSG.ClassicalInvolution.RouteD.PatternC
public import CFSG.ClassicalInvolution.RouteD.Entries

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

variable {n : ℕ}

instance (i j : Fin n) : Decidable (DAdj n i j) := by unfold DAdj; infer_instance

theorem D_mod2 (i j : Fin n) : ((CartanMatrix.D n i j : ℤ) : ZMod 2) =
    if DAdj n i j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    have h1 : ¬ DAdj n i i := by unfold DAdj; omega
    simp only [CartanMatrix.D_diag, h1, ↓reduceIte]
    decide
  · by_cases hd : DAdj n i j
    · have := (D_eq_neg_one_iff i j).mpr hd
      simp only [this, hd, ↓reduceIte]
      decide
    · have := (D_eq_zero_iff i j).mpr ⟨h, hd⟩
      simp only [this, hd, ↓reduceIte]
      decide

theorem DAdj_iff_chain {i j : Fin n} (hi : i.val + 2 ≤ n) (hj : j.val + 2 ≤ n) :
    DAdj n i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  unfold DAdj; omega

theorem DAdj_last {i j : Fin n} (hi : i.val + 2 ≤ n) (hj : j.val + 1 = n) :
    DAdj n i j ↔ i.val + 3 = n := by
  unfold DAdj; omega

theorem DAdj_of_last {i j : Fin n} (hi : i.val + 1 = n) : DAdj n i j ↔ j.val + 3 = n := by
  unfold DAdj; omega

@[expose] def picD (n : ℕ) (t : ℕ → ZMod 2) (c : ZMod 2) : Fin n → ZMod 2 :=
  fun j => if j.val + 1 < n then t j + t (j + 1) else t (n - 2) + t (n - 1) + c

theorem charRefl_picD_swap (i : ℕ) (hi : i + 1 < n) (t : ℕ → ZMod 2) (c : ZMod 2) :
    charRefl (CartanMatrix.D n) ⟨i, by omega⟩ (picD n t c) = picD n (swapAt t i) c := by
  funext j
  have hj := j.isLt
  simp only [charRefl, picD, D_mod2, hi, ↓reduceIte]
  by_cases hjn : (j : ℕ) + 1 < n
  · simp only [hjn, ↓reduceIte]
    have hadj : (if DAdj n ⟨i, by omega⟩ j then (1 : ZMod 2) else 0) =
        if (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) then 1 else 0 := by
      have : DAdj n ⟨i, by omega⟩ j ↔ (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) :=
        DAdj_iff_chain (by simp only; omega) (by omega)
      simp only [this]
    rw [hadj]
    by_cases hji : (j : ℕ) = i
    · simp only [show ¬ (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) by omega, ↓reduceIte, zero_mul, add_zero]
      simp only [hji, swapAt_left, swapAt_right]
      exact add_comm _ _
    · by_cases hj1 : (j : ℕ) + 1 = i
      · have key : ∀ x y z : ZMod 2, x + y + (y + z) = x + z := by decide
        have e1 : swapAt t i j = t j := swapAt_of_ne hji (by omega)
        have e2 : swapAt t i (j + 1) = t (i + 1) := by rw [hj1, swapAt_left]
        simp only [show (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) by omega, ↓reduceIte, one_mul]
        rw [e1, e2, hj1]
        exact key _ _ _
      · by_cases hi1 : i + 1 = (j : ℕ)
        · have key : ∀ x y z : ZMod 2, y + z + (x + y) = x + z := by decide
          simp only [show (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) by omega, ↓reduceIte, one_mul]
          rw [← hi1, swapAt_right, swapAt_of_ne (by omega) (by omega)]
          exact key _ _ _
        · simp only [show ¬ (i + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = i) by omega, ↓reduceIte, zero_mul,
            add_zero]
          rw [swapAt_of_ne hji (by omega),
            swapAt_of_ne (show (j : ℕ) + 1 ≠ i by omega) (show (j : ℕ) + 1 ≠ i + 1 by omega)]
  · have hj1 : (j : ℕ) = n - 1 := by omega
    simp only [hjn, ↓reduceIte]
    have hadj : (if DAdj n ⟨i, by omega⟩ j then (1 : ZMod 2) else 0) =
        if i + 3 = n then 1 else 0 := by
      have : DAdj n ⟨i, by omega⟩ j ↔ i + 3 = n := DAdj_last (by simp only; omega) (by omega)
      simp only [this]
    rw [hadj]
    by_cases h3 : i + 3 = n
    · have e1 : n - 2 = i + 1 := by omega
      have e2 : n - 1 = i + 2 := by omega
      have key : ∀ a b d c : ZMod 2, (b + d + c) + (a + b) = a + d + c := by decide
      simp only [h3, ↓reduceIte, one_mul, e1, e2]
      rw [swapAt_right, swapAt_of_ne (by omega) (by omega)]
      exact key _ _ _ _
    · simp only [h3, ↓reduceIte, zero_mul, add_zero]
      by_cases h2 : i + 2 = n
      · have e1 : n - 2 = i := by omega
        have e2 : n - 1 = i + 1 := by omega
        rw [e1, e2, swapAt_left, swapAt_right]
        have key : ∀ a b c : ZMod 2, a + b + c = b + a + c := by decide
        exact key _ _ _
      · rw [swapAt_of_ne (show n - 2 ≠ i by omega) (show n - 2 ≠ i + 1 by omega),
          swapAt_of_ne (show n - 1 ≠ i by omega) (show n - 1 ≠ i + 1 by omega)]

@[expose] def swapFlip (n : ℕ) (t : ℕ → ZMod 2) (c : ZMod 2) : ℕ → ZMod 2 :=
  fun m => if m = n - 2 then t (n - 1) + c else if m = n - 1 then t (n - 2) + c else t m

theorem charRefl_picD_last (hn : 4 ≤ n) (t : ℕ → ZMod 2) (c : ZMod 2) :
    charRefl (CartanMatrix.D n) ⟨n - 1, by omega⟩ (picD n t c) = picD n (swapFlip n t c) c := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  funext j
  have hj := j.isLt
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 1 = m + 3 := by omega
  have hnn : ¬ (m + 3 + 1 < m + 4) := by omega
  simp only [charRefl, picD, D_mod2, hnn, ↓reduceIte, swapFlip, e2, e3]
  have hadj : (if DAdj (m + 4) ⟨m + 3, by omega⟩ j then (1 : ZMod 2) else 0) =
      if (j : ℕ) = m + 1 then 1 else 0 := by
    have : DAdj (m + 4) ⟨m + 3, by omega⟩ j ↔ (j : ℕ) = m + 1 := by
      rw [DAdj_of_last (by show m + 3 + 1 = m + 4; rfl)]; omega
    simp only [this]
  rw [hadj]
  by_cases hjn : (j : ℕ) + 1 < m + 4
  · simp only [hjn, ↓reduceIte]
    by_cases h1 : (j : ℕ) = m + 1
    · have key : ∀ a b d c : ZMod 2, (a + b) + (b + d + c) = a + (d + c) := by decide
      simp only [h1, ↓reduceIte, one_mul]
      simp only [show ¬ (m + 1 = m + 2) by omega, show ¬ (m + 1 = m + 3) by omega, ↓reduceIte]
      exact key _ _ _ _
    · simp only [h1, ↓reduceIte, zero_mul, add_zero]
      by_cases h2 : (j : ℕ) = m + 2
      · have key : ∀ a b c : ZMod 2, a + b = (b + c) + (a + c) := by decide
        simp only [h2, ↓reduceIte]
        simp only [show ¬ (m + 2 + 1 = m + 2) by omega, ↓reduceIte]
        exact key _ _ _
      · simp only [show ¬ ((j : ℕ) = m + 2) by omega, show ¬ ((j : ℕ) = m + 3) by omega,
          show ¬ ((j : ℕ) + 1 = m + 2) by omega, show ¬ ((j : ℕ) + 1 = m + 3) by omega,
          ↓reduceIte]
  · have h3 : (j : ℕ) = m + 3 := by omega
    simp only [hjn, ↓reduceIte]
    have key : ∀ a b c : ZMod 2, a + b + c = (b + c + (a + c)) + c := by decide
    simp only [show ¬ ((j : ℕ) = m + 1) by omega, show ¬ (m + 3 = m + 2) by omega, ↓reduceIte,
      zero_mul, add_zero]
    exact key _ _ _

@[expose] def flip2 (t : ℕ → ZMod 2) (k l : ℕ) (c : ZMod 2) : ℕ → ZMod 2 :=
  addAt (addAt t k c) l c

theorem swap_swapFlip (hn : 2 ≤ n) (t : ℕ → ZMod 2) (c : ZMod 2) :
    swapAt (swapFlip n t c) (n - 2) = flip2 t (n - 2) (n - 1) c := by
  funext m
  by_cases h1 : m = n - 2
  · subst h1
    simp only [swapAt, ↓reduceIte, swapFlip, flip2, addAt]
    simp [show n - 2 + 1 = n - 1 by omega, show n - 2 ≠ n - 1 by omega,
      show n - 1 ≠ n - 2 by omega]
  · by_cases h2 : m = n - 1
    · subst h2
      have e : n - 2 + 1 = n - 1 := by omega
      simp only [swapAt, flip2, addAt, swapFlip, e, show n - 1 ≠ n - 2 by omega, ↓reduceIte]
    · simp only [swapAt, flip2, addAt, swapFlip, h1, h2, show m ≠ n - 2 + 1 by omega, ↓reduceIte]

theorem swap_flip2_swap {k l : ℕ} (hk : k + 1 < l) (t : ℕ → ZMod 2) (c : ZMod 2) :
    swapAt (flip2 (swapAt t k) (k + 1) l c) k = flip2 t k l c := by
  funext m
  by_cases h1 : m = k
  · subst h1
    simp only [swapAt, flip2, addAt, ↓reduceIte, show m + 1 ≠ m by omega, show m ≠ l by omega,
      show m + 1 ≠ l by omega]
  · by_cases h2 : m = k + 1
    · subst h2
      simp only [swapAt, flip2, addAt, ↓reduceIte, h1, show k + 1 ≠ l by omega,
        show k ≠ l by omega, show k ≠ k + 1 by omega]
    · by_cases h3 : m = l
      · subst h3
        simp only [swapAt, flip2, addAt, ↓reduceIte, h1, h2]
      · simp only [swapAt, flip2, addAt, ↓reduceIte, h1, h2, h3]

theorem reach_flipPair_D (hn : 4 ≤ n) : ∀ (d k : ℕ), k + 2 + d = n → ∀ t : ℕ → ZMod 2,
    CharReach (CartanMatrix.D n) (picD n t 1) (picD n (flip2 t k (n - 1) 1) 1) := by
  intro d
  induction d with
  | zero =>
    intro k hk t
    have hk' : k = n - 2 := by omega
    subst hk'
    have s1 := charRefl_picD_last hn t 1
    have s2 := charRefl_picD_swap (n := n) (n - 2) (by omega) (swapFlip n t 1) 1
    rw [swap_swapFlip (by omega)] at s2
    have step1 : CharReach (CartanMatrix.D n) (picD n t 1) (picD n (swapFlip n t 1) 1) := by
      rw [← s1]; exact CharReach.single' _ _
    have step2 : CharReach (CartanMatrix.D n) (picD n (swapFlip n t 1) 1)
        (picD n (flip2 t (n - 2) (n - 1) 1) 1) := by
      rw [← s2]; exact CharReach.single' _ _
    exact step1.trans' step2
  | succ d ih =>
    intro k hk t
    have hkn : k + 1 < n := by omega
    have s1 := charRefl_picD_swap (n := n) k hkn t 1
    have s2 := charRefl_picD_swap (n := n) k hkn (flip2 (swapAt t k) (k + 1) (n - 1) 1) 1
    rw [swap_flip2_swap (by omega)] at s2
    have step1 : CharReach (CartanMatrix.D n) (picD n t 1) (picD n (swapAt t k) 1) := by
      rw [← s1]; exact CharReach.single' _ _
    have step2 : CharReach (CartanMatrix.D n) (picD n (flip2 (swapAt t k) (k + 1) (n - 1) 1) 1)
        (picD n (flip2 t k (n - 1) 1) 1) := by
      rw [← s2]; exact CharReach.single' _ _
    exact (step1.trans' (ih (k + 1) (by omega) _)).trans' step2

theorem reach_zero_D (hn : 4 ≤ n) (t : ℕ → ZMod 2) : ∀ m, m ≤ n - 1 →
    ∃ t' : ℕ → ZMod 2, (∀ k, k < m → t' k = 0) ∧ (∀ k, m ≤ k → k ≤ n - 2 → t' k = t k) ∧
      CharReach (CartanMatrix.D n) (picD n t 1) (picD n t' 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨t, fun k hk => absurd hk (by omega), fun k _ _ => rfl, CharReach.refl' _ _⟩
  | succ m ih =>
    intro hm
    obtain ⟨t', h1, h2, h3⟩ := ih (by omega)
    by_cases htm : t' m = 0
    · refine ⟨t', fun k hk => ?_, fun k hk hk' => h2 k (by omega) hk', h3⟩
      by_cases hkm : k < m
      · exact h1 k hkm
      · have : k = m := by omega
        subst this; exact htm
    · have htm1 : t' m = 1 := by revert htm; generalize t' m = x; revert x; decide
      have hflip := reach_flipPair_D hn (n - m - 2) m (by omega) t'
      refine ⟨flip2 t' m (n - 1) 1, fun k hk => ?_, fun k hk hk' => ?_, h3.trans' hflip⟩
      · by_cases hkm : k < m
        · simp only [flip2, addAt, show k ≠ n - 1 by omega, show k ≠ m by omega, ↓reduceIte]
          exact h1 k hkm
        · have : k = m := by omega
          subst this
          simp only [flip2, addAt, show k ≠ n - 1 by omega, ↓reduceIte, htm1]
          decide
      · simp only [flip2, addAt, show k ≠ n - 1 by omega, show k ≠ m by omega, ↓reduceIte]
        exact h2 k (by omega) hk'

theorem picD_compl (t : ℕ → ZMod 2) (c : ZMod 2) :
    picD n (fun k => t k + 1) c = picD n t c := by
  funext j
  have key : ∀ a b : ZMod 2, (a + 1) + (b + 1) = a + b := by decide
  have key2 : ∀ a b c : ZMod 2, (a + 1) + (b + 1) + c = a + b + c := by decide
  simp only [picD]
  split_ifs
  · exact key _ _
  · exact key2 _ _ _

theorem picD_prefixSum (hn : 2 ≤ n) (v : Fin n → ZMod 2) :
    picD n (prefixSum v) (v ⟨n - 1, by omega⟩ + v ⟨n - 2, by omega⟩) = v := by
  funext j
  have key : ∀ x y : ZMod 2, x + (x + y) = y := by decide
  have h := congrFun (picA_prefixSum v) j
  simp only [picD]
  by_cases hj : (j : ℕ) + 1 < n
  · simp only [hj, ↓reduceIte]
    exact h
  · have hj1 : (j : ℕ) = n - 1 := by have := j.isLt; omega
    have h2 := congrFun (picA_prefixSum v) ⟨n - 2, by omega⟩
    simp only [picA] at h2
    simp only [hj, ↓reduceIte]
    have e : n - 2 + 1 = n - 1 := by omega
    rw [e] at h2
    rw [h2]
    have hjv : j = ⟨n - 1, by omega⟩ := Fin.ext hj1
    have key3 : ∀ x y : ZMod 2, x + (y + x) = y := by decide
    exact (key3 _ _).trans (congrArg v hjv.symm)

theorem picD_last_pattern (hn : 2 ≤ n) (t' : ℕ → ZMod 2) (h1 : ∀ k, k + 1 < n → t' k = 0) :
    ∀ j : Fin n, picD n t' 1 j =
      if (j : ℕ) + 2 = n then t' (n - 1) else if (j : ℕ) + 1 = n then t' (n - 1) + 1 else 0 := by
  intro j
  have hjn := j.isLt
  simp only [picD]
  by_cases hj : (j : ℕ) + 1 < n
  · simp only [hj, ↓reduceIte]
    by_cases hj2 : (j : ℕ) + 2 = n
    · have e : (j : ℕ) + 1 = n - 1 := by omega
      rw [h1 j hj, e]
      simp only [hj2, ↓reduceIte, zero_add]
    · have e : (j : ℕ) + 2 < n := by omega
      rw [h1 j hj, h1 (j + 1) e]
      simp only [hj2, show ¬ ((j : ℕ) + 1 = n) by omega, ↓reduceIte, add_zero]
  · have hj1 : (j : ℕ) + 1 = n := by omega
    simp only [hj1, show ¬ ((j : ℕ) + 2 = n) by omega, lt_self_iff_false, ↓reduceIte]
    rw [h1 (n - 2) (by omega)]
    simp only [zero_add]

theorem patternLemma_D (hn : 4 ≤ n) : PatternLemma (CartanMatrix.D n) := by
  intro v hv
  set t := prefixSum v with ht
  set c : ZMod 2 := v ⟨n - 1, by omega⟩ + v ⟨n - 2, by omega⟩ with hc
  have hpic : picD n t c = v := picD_prefixSum (by omega) v
  have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases key c with hc0 | hc1
  ·
    obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨j1, hj1n, hj1⟩ : ∃ j : Fin n, (j : ℕ) + 1 < n ∧ v j ≠ 0 := by
      by_cases hj : (j0 : ℕ) + 1 < n
      · exact ⟨j0, hj, hj0⟩
      · have hj0' : j0 = ⟨n - 1, by omega⟩ := Fin.ext (by have := j0.isLt; simp only; omega)
        refine ⟨⟨n - 2, by omega⟩, by simp only; omega, ?_⟩
        intro h
        apply hj0
        rw [hj0']
        have key2 : ∀ x y : ZMod 2, x + y = 0 → y = 0 → x = 0 := by decide
        exact key2 _ _ (by rw [← hc]; exact hc0) h
    have hmix : (∃ k, k < n ∧ t k = 0) ∧ (∃ k, k < n ∧ t k = 1) := by
      have h1 : t j1 + t (j1 + 1) = v j1 := by
        rw [← hpic]; simp [picD, hj1n]
      have key2 : ∀ x y : ZMod 2, x + y ≠ 0 → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
      rcases key2 _ _ (by rw [h1]; exact hj1) with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact ⟨⟨j1, by omega, h2⟩, ⟨j1 + 1, hj1n, h3⟩⟩
      · exact ⟨⟨j1 + 1, hj1n, h3⟩, ⟨j1, by omega, h2⟩⟩
    obtain ⟨t', a, hr, ha, hs, hfix⟩ := sort_swaps 0 n t
    have hreach := lift_swaps (A := CartanMatrix.D n) (fun t => picD n t c) n
      (fun i hi => ⟨i, by omega⟩) (fun i hi t => charRefl_picD_swap i hi t c) hr
    rw [hpic] at hreach
    have hm0 := reflTransGen_Sw_val_pres hr 0 hmix.1
    have hm1 := reflTransGen_Sw_val_pres hr 1 hmix.2
    obtain ⟨ha0, ha1⟩ := sorted_cut (u := 0) hs (by simpa using hm0) (by simpa using hm1)
    by_cases ha2 : a + 2 ≤ n
    · refine ⟨picD n t' c, hreach, ⟨a - 1, by omega⟩, ?_⟩
      funext j
      have hjn := j.isLt
      simp only [picD, Pi.single_apply, Fin.ext_iff, hc0]
      by_cases hj : (j : ℕ) + 1 < n
      · rw [hs j (by omega), hs (j + 1) hj]
        simp only [hj, ↓reduceIte]
        by_cases h1 : (j : ℕ) < a
        · by_cases h2 : (j : ℕ) + 1 < a
          · have h3 : ¬ ((j : ℕ) = a - 1) := by omega
            simp only [h1, h2, h3, ↓reduceIte, add_zero]
          · have h3 : (j : ℕ) = a - 1 := by omega
            simp only [h1, h2, ↓reduceIte]
            simp only [h3, ↓reduceIte]
            decide
        · have h2 : ¬ ((j : ℕ) + 1 < a) := by omega
          have h3 : ¬ ((j : ℕ) = a - 1) := by omega
          simp only [h1, h2, h3, ↓reduceIte]
          decide
      · rw [hs (n - 2) (by omega), hs (n - 1) (by omega)]
        simp only [hj, ↓reduceIte, show ¬ (n - 2 < a) by omega, show ¬ (n - 1 < a) by omega]
        have h3 : ¬ ((j : ℕ) = a - 1) := by omega
        simp only [h3, ↓reduceIte]
        decide
    ·
      have han : a = n - 1 := by omega
      have hcompl : picD n (fun k => t' k + 1) c = picD n t' c := picD_compl t' c
      rw [← hcompl] at hreach
      obtain ⟨t₂, hr2, h1, h2, h3⟩ := bubble_left 0 (n - 1) 0 (by omega) (fun k => t' k + 1)
        (fun k hk => absurd hk (by omega))
        (fun k _ hk => by
          have := hs k (by omega)
          simp only [show k < a by omega, ↓reduceIte] at this
          simp only [this])
        (by
          have := hs (n - 1) (by omega)
          simp only [show ¬ (n - 1 < a) by omega, ↓reduceIte] at this
          simp only [this]
          decide)
      rw [show n - 1 + 1 = n by omega] at hr2
      have hreach2 := lift_swaps (A := CartanMatrix.D n) (fun t => picD n t c) n
        (fun i hi => ⟨i, by omega⟩) (fun i hi t => charRefl_picD_swap i hi t c) hr2
      refine ⟨picD n t₂ c, hreach.trans' hreach2, ⟨0, by omega⟩, ?_⟩
      funext j
      have hjn := j.isLt
      simp only [picD, Pi.single_apply, Fin.ext_iff, hc0]
      by_cases hj : (j : ℕ) + 1 < n
      · by_cases hj0 : (j : ℕ) = 0
        · rw [hj0, h1 0 (by omega), h2 1 (by omega) (by omega)]
          simp only [↓reduceIte, zero_add, show 1 < n by omega]
        · rw [h2 j (by omega) (by omega), h2 (j + 1) (by omega) (by omega)]
          simp only [hj, hj0, ↓reduceIte]
          decide
      · rw [h2 (n - 2) (by omega) (by omega), h2 (n - 1) (by omega) (by omega)]
        simp only [hj, show (j : ℕ) ≠ 0 by omega, ↓reduceIte]
        decide
  ·
    obtain ⟨t', h1, h2, h3⟩ := reach_zero_D hn t (n - 1) le_rfl
    rw [hc1] at hpic
    have hreach : CharReach (CartanMatrix.D n) v (picD n t' 1) := by rw [← hpic]; exact h3
    have h1' : ∀ k, k + 1 < n → t' k = 0 := fun k hk => h1 k (by omega)
    have hpat := picD_last_pattern (n := n) (by omega) t' h1'
    rcases key (t' (n - 1)) with he | he
    · refine ⟨picD n t' 1, hreach, ⟨n - 1, by omega⟩, ?_⟩
      funext j
      rw [hpat j, he]
      simp only [Pi.single_apply, Fin.ext_iff]
      have e : ((j : ℕ) = n - 1) ↔ ((j : ℕ) + 1 = n) := by have := j.isLt; omega
      simp only [e]
      by_cases hj2 : (j : ℕ) + 2 = n
      · have hn' : ¬ ((j : ℕ) + 1 = n) := by omega
        simp only [hj2, hn', ↓reduceIte]
      · by_cases hj1 : (j : ℕ) + 1 = n
        · simp only [hj2, hj1, ↓reduceIte]
          decide
        · simp only [hj2, hj1, ↓reduceIte]
    · refine ⟨picD n t' 1, hreach, ⟨n - 2, by omega⟩, ?_⟩
      funext j
      rw [hpat j, he]
      simp only [Pi.single_apply, Fin.ext_iff]
      have e : ((j : ℕ) = n - 2) ↔ ((j : ℕ) + 2 = n) := by have := j.isLt; omega
      simp only [e]
      by_cases hj2 : (j : ℕ) + 2 = n
      · simp only [hj2, ↓reduceIte]
      · by_cases hj1 : (j : ℕ) + 1 = n
        · simp only [hj2, hj1, ↓reduceIte]
          decide
        · simp only [hj2, hj1, ↓reduceIte]

end CFSG.ClassicalInvolution.RouteD
