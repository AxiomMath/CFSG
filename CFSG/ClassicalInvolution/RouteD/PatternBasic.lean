module

public import CFSG.ClassicalInvolution.RouteD.Basic

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti

@[expose] def charRefl {ι : Type} (A : Matrix ι ι ℤ) (i : ι) (v : ι → ZMod 2) : ι → ZMod 2 :=
  fun j => v j + (A i j : ZMod 2) * v i

@[expose] def CharReach {ι : Type} (A : Matrix ι ι ℤ) : (ι → ZMod 2) → (ι → ZMod 2) → Prop :=
  Relation.ReflTransGen fun v w => ∃ i, w = charRefl A i v

@[expose] def SupportOne {ι : Type} [DecidableEq ι] (w : ι → ZMod 2) : Prop :=
  ∃ j, w = Pi.single j 1

@[expose] def PatternLemma {ι : Type} [DecidableEq ι] (A : Matrix ι ι ℤ) : Prop :=
  ∀ v : ι → ZMod 2, v ≠ 0 → ∃ w, CharReach A v w ∧ SupportOne w

theorem CharReach.refl' {ι : Type} (A : Matrix ι ι ℤ) (v : ι → ZMod 2) : CharReach A v v :=
  Relation.ReflTransGen.refl

theorem CharReach.single' {ι : Type} {A : Matrix ι ι ℤ} (i : ι) (v : ι → ZMod 2) :
    CharReach A v (charRefl A i v) :=
  Relation.ReflTransGen.single ⟨i, rfl⟩

theorem CharReach.trans' {ι : Type} {A : Matrix ι ι ℤ} {u v w : ι → ZMod 2}
    (h1 : CharReach A u v) (h2 : CharReach A v w) : CharReach A u w :=
  Relation.ReflTransGen.trans h1 h2

@[expose] def swapAt (t : ℕ → ZMod 2) (i : ℕ) : ℕ → ZMod 2 :=
  fun k => if k = i then t (i + 1) else if k = i + 1 then t i else t k

@[expose] def Sw (m : ℕ) (t t' : ℕ → ZMod 2) : Prop := ∃ i, i + 1 < m ∧ t' = swapAt t i

theorem lift_swaps {ι : Type} {A : Matrix ι ι ℤ} (φ : (ℕ → ZMod 2) → ι → ZMod 2) (m : ℕ)
    (node : ∀ i, i + 1 < m → ι)
    (h : ∀ i (hi : i + 1 < m) t, charRefl A (node i hi) (φ t) = φ (swapAt t i))
    {t t' : ℕ → ZMod 2} (hr : Relation.ReflTransGen (Sw m) t t') : CharReach A (φ t) (φ t') := by
  induction hr with
  | refl => exact CharReach.refl' _ _
  | tail _ hs ih =>
    obtain ⟨i, hi, rfl⟩ := hs
    exact ih.trans' (by rw [← h i hi]; exact CharReach.single' _ _)

theorem swapAt_of_ne {t : ℕ → ZMod 2} {i k : ℕ} (h1 : k ≠ i) (h2 : k ≠ i + 1) :
    swapAt t i k = t k := by
  simp [swapAt, h1, h2]

theorem swapAt_left (t : ℕ → ZMod 2) (i : ℕ) : swapAt t i i = t (i + 1) := by
  simp [swapAt]

theorem swapAt_right (t : ℕ → ZMod 2) (i : ℕ) : swapAt t i (i + 1) = t i := by
  simp [swapAt]

theorem swapAt_swapAt (t : ℕ → ZMod 2) (i : ℕ) : swapAt (swapAt t i) i = t := by
  funext k
  simp only [swapAt]
  split_ifs <;> first | rfl | omega | simp_all

theorem Sw.mono {m m' : ℕ} (h : m ≤ m') {t t' : ℕ → ZMod 2} (hs : Sw m t t') : Sw m' t t' := by
  obtain ⟨i, hi, e⟩ := hs
  exact ⟨i, by omega, e⟩

theorem reflTransGen_Sw_mono {m m' : ℕ} (h : m ≤ m') {t t' : ℕ → ZMod 2}
    (hr : Relation.ReflTransGen (Sw m) t t') : Relation.ReflTransGen (Sw m') t t' := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Sw.mono h hs)

theorem bubble_left (u : ZMod 2) (m a : ℕ) (ha : a ≤ m) (t₁ : ℕ → ZMod 2)
    (hlow : ∀ k, k < a → t₁ k = u) (hmid : ∀ k, a ≤ k → k < m → t₁ k = u + 1)
    (hm : t₁ m = u) :
    ∃ t₂, Relation.ReflTransGen (Sw (m + 1)) t₁ t₂ ∧ (∀ k, k < a + 1 → t₂ k = u) ∧
      (∀ k, a < k → k ≤ m → t₂ k = u + 1) ∧ ∀ k, m < k → t₂ k = t₁ k := by
  have key : ∀ d, a + d ≤ m → ∃ t₂, Relation.ReflTransGen (Sw (m + 1)) t₁ t₂ ∧
      (∀ k, k < a → t₂ k = u) ∧ (∀ k, a ≤ k → k + d < m → t₂ k = u + 1) ∧ t₂ (m - d) = u ∧
      (∀ k, m - d < k → k ≤ m → t₂ k = u + 1) ∧ ∀ k, m < k → t₂ k = t₁ k := by
    intro d
    induction d with
    | zero =>
      intro _
      exact ⟨t₁, Relation.ReflTransGen.refl, fun k hk => hlow k hk,
        fun k hk hkm => hmid k hk (by omega), by simpa using hm,
        fun k hk hkm => absurd hk (by omega), fun k _ => rfl⟩
    | succ d ih =>
      intro hd
      obtain ⟨t₂, hr, h1, h2, h3, h4, h5⟩ := ih (by omega)
      have hp : t₂ (m - d - 1) = u + 1 := h2 (m - d - 1) (by omega) (by omega)
      have hp1 : t₂ (m - d - 1 + 1) = u := by rw [show m - d - 1 + 1 = m - d by omega]; exact h3
      refine ⟨swapAt t₂ (m - d - 1),
        hr.tail ⟨m - d - 1, by omega, rfl⟩, fun k hk => ?_, fun k hk hkm => ?_, ?_,
        fun k hk hkm => ?_, fun k hk => ?_⟩
      · rw [swapAt_of_ne (by omega) (by omega)]
        exact h1 k hk
      · rw [swapAt_of_ne (by omega) (by omega)]
        exact h2 k hk (by omega)
      · rw [show m - (d + 1) = m - d - 1 by omega, swapAt_left]
        exact hp1
      · by_cases hk1 : k = m - d - 1 + 1
        · rw [hk1, swapAt_right, hp]
        · rw [swapAt_of_ne (by omega) hk1]
          exact h4 k (by omega) hkm
      · rw [swapAt_of_ne (by omega) (by omega)]
        exact h5 k hk
  obtain ⟨t₂, hr, h1, h2, h3, h4, h5⟩ := key (m - a) (by omega)
  refine ⟨t₂, hr, fun k hk => ?_, fun k hk hkm => h4 k (by omega) hkm, h5⟩
  by_cases hka : k < a
  · exact h1 k hka
  · have : k = a := by omega
    subst this
    rw [show m - (m - k) = k by omega] at h3
    exact h3

theorem sort_swaps (u : ZMod 2) : ∀ (m : ℕ) (t : ℕ → ZMod 2), ∃ (t' : ℕ → ZMod 2) (a : ℕ),
    Relation.ReflTransGen (Sw m) t t' ∧ a ≤ m ∧
      (∀ k, k < m → t' k = if k < a then u else u + 1) ∧ ∀ k, m ≤ k → t' k = t k := by
  intro m
  induction m with
  | zero =>
    intro t
    exact ⟨t, 0, Relation.ReflTransGen.refl, le_refl _, fun k hk => absurd hk (by omega),
      fun k _ => rfl⟩
  | succ m ih =>
    intro t
    obtain ⟨t₁, a, hr, ha, hs, hfix⟩ := ih t
    have hr' : Relation.ReflTransGen (Sw (m + 1)) t t₁ := reflTransGen_Sw_mono (by omega) hr
    have hm : t₁ m = t m := hfix m le_rfl
    by_cases hum : t m = u + 1
    · refine ⟨t₁, a, hr', by omega, fun k hk => ?_, fun k hk => hfix k (by omega)⟩
      by_cases hkm : k < m
      · exact hs k hkm
      · have : k = m := by omega
        subst this
        have : ¬ (k < a) := by omega
        simp [hm, hum, this]
    · have key : ∀ x u : ZMod 2, x ≠ u + 1 → x = u := by decide
      have hum' : t₁ m = u := by rw [hm]; exact key _ _ hum
      obtain ⟨t₂, hr2, h1, h2, h3⟩ := bubble_left u m a ha t₁
        (fun k hk => by have := hs k (by omega); simpa [hk] using this)
        (fun k hk hkm => by have := hs k hkm; simpa [show ¬ k < a by omega] using this) hum'
      refine ⟨t₂, a + 1, hr'.trans hr2, by omega, fun k hk => ?_, fun k hk => ?_⟩
      · by_cases hka : k < a + 1
        · simp [hka, h1 k hka]
        · simp [hka, h2 k (by omega) (by omega)]
      · rw [h3 k (by omega)]
        exact hfix k (by omega)

theorem Sw.val_pres {m : ℕ} {t t' : ℕ → ZMod 2} (hs : Sw m t t') (x : ZMod 2)
    (h : ∃ k, k < m ∧ t k = x) : ∃ k, k < m ∧ t' k = x := by
  obtain ⟨i, hi, rfl⟩ := hs
  obtain ⟨k, hk, hkx⟩ := h
  by_cases h1 : k = i
  · exact ⟨i + 1, hi, by rw [swapAt_right, ← h1, hkx]⟩
  · by_cases h2 : k = i + 1
    · exact ⟨i, by omega, by rw [swapAt_left, ← h2, hkx]⟩
    · exact ⟨k, hk, by rw [swapAt_of_ne h1 h2, hkx]⟩

theorem reflTransGen_Sw_val_pres {m : ℕ} {t t' : ℕ → ZMod 2}
    (hr : Relation.ReflTransGen (Sw m) t t') (x : ZMod 2) (h : ∃ k, k < m ∧ t k = x) :
    ∃ k, k < m ∧ t' k = x := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact hs.val_pres x ih

theorem sorted_cut {u : ZMod 2} {m a : ℕ} {t : ℕ → ZMod 2}
    (hs : ∀ k, k < m → t k = if k < a then u else u + 1) (h0 : ∃ k, k < m ∧ t k = u)
    (h1 : ∃ k, k < m ∧ t k = u + 1) : 0 < a ∧ a < m := by
  have e : ∀ u : ZMod 2, u ≠ u + 1 := by decide
  obtain ⟨k0, hk0, hk0v⟩ := h0
  obtain ⟨k1, hk1, hk1v⟩ := h1
  rw [hs k0 hk0] at hk0v
  rw [hs k1 hk1] at hk1v
  constructor
  · by_contra h
    have : ¬ k0 < a := by omega
    simp only [this, ↓reduceIte] at hk0v
    exact e u hk0v.symm
  · by_contra h
    have : k1 < a := by omega
    simp only [this, ↓reduceIte] at hk1v
    exact e u hk1v

end CFSG.ClassicalInvolution.RouteD
