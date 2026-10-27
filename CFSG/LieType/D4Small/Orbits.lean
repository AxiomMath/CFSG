module

public import CFSG.LieType.D4Small.WeightClass
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.D4Small

open Matrix

attribute [local instance] Classical.propDecidable

@[expose] def IsVWt {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) : Prop :=
  ∃ i, a = Pi.single i b ∨ a = Pi.single i (-b)

@[expose] def IsSWt {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) : Prop :=
  ∀ i, a i = b ∨ a i = -b

@[expose] noncomputable def negCount {N : ℕ} (b : ZMod N) (a : Fin 4 → ZMod N) : ℕ :=
  (Finset.univ.filter fun i => a i = -b).card

@[expose] def IsSmallWt {N : ℕ} (a : Fin 4 → ZMod N) : Prop :=
  a = 0 ∨ (∃ b ≠ 0, IsVWt b a) ∨ ∃ b ≠ 0, IsSWt b a

@[expose] def Closed {N : ℕ} (S : Finset (Fin 4 → ZMod N)) : Prop :=
  ∀ β, IsD4Root β → ∀ a ∈ S, reflW β a ∈ S

private theorem ne_neg_of_ne_zero {N : ℕ} (hN : Odd N) {x : ZMod N} (hx : x ≠ 0) : x ≠ -x :=
  ZMod.ne_neg_self hN hx

private theorem neg_ne_zero {N : ℕ} {x : ZMod N} (hx : x ≠ 0) : -x ≠ 0 := by
  simpa using hx

private def swap {N : ℕ} (i j : Fin 4) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  reflW (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) a

private def flip {N : ℕ} (i j : Fin 4) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  reflW (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) a

private def negTwo {N : ℕ} (i j : Fin 4) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  swap i j (flip i j a)

theorem castW_single {N : ℕ} (i : Fin 4) (c : ℤ) :
    castW N (Pi.single i c) = Pi.single i (c : ZMod N) := by
  funext k
  by_cases h : k = i <;> simp [castW, Pi.single_apply, h]

theorem dotProduct_castW_single_sub_single {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4}
    (hij : i ≠ j) :
    a ⬝ᵥ castW N (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) = a i - a j := by
  rw [castW_sub N, castW_single, castW_single]
  simp [dotProduct_sub, dotProduct_single_one]

theorem dotProduct_castW_single_add_single {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4}
    (hij : i ≠ j) :
    a ⬝ᵥ castW N (Pi.single i (1 : ℤ) + Pi.single j (1 : ℤ)) = a i + a j := by
  rw [castW_add N, castW_single, castW_single]
  simp [dotProduct_add, dotProduct_single_one]

theorem isD4Root_single_sub_single {i j : Fin 4} (hij : i ≠ j) :
    IsD4Root (Pi.single i (1 : ℤ) - Pi.single j (1 : ℤ)) := by
  simpa [sub_eq_add_neg, Pi.single_neg] using
    (isD4Root_single_add_single hij (s := 1) (t := -1) (Or.inl rfl) (Or.inr rfl))

private theorem swap_apply_left {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    swap i j a i = a j := by
  have hdot := dotProduct_castW_single_sub_single a hij
  simp [swap, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hdot]

private theorem swap_apply_right {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    swap i j a j = a i := by
  have hdot := dotProduct_castW_single_sub_single a hij
  simp [swap, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hdot]

private theorem swap_apply_of_ne {N : ℕ} (a : Fin 4 → ZMod N) {i j k : Fin 4} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : swap i j a k = a k := by
  have hdot := dotProduct_castW_single_sub_single a hij
  simp [swap, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hki, hkj, hdot]

private theorem flip_apply_left {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    flip i j a i = -a j := by
  have hdot := dotProduct_castW_single_add_single a hij
  simp [flip, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hdot]

private theorem flip_apply_right {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    flip i j a j = -a i := by
  have hdot := dotProduct_castW_single_add_single a hij
  simp [flip, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hdot]

private theorem flip_apply_of_ne {N : ℕ} (a : Fin 4 → ZMod N) {i j k : Fin 4} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : flip i j a k = a k := by
  have hdot := dotProduct_castW_single_add_single a hij
  simp [flip, reflW, castW, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, hij, hki, hkj, hdot]

private theorem swap_apply {N : ℕ} (a : Fin 4 → ZMod N) {i j k : Fin 4} (hij : i ≠ j) :
    swap i j a k = if k = i then a j else if k = j then a i else a k := by
  by_cases hki : k = i
  · subst hki; simp [swap_apply_left a hij]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, swap_apply_right a hij]
    · simp [hki, hkj, swap_apply_of_ne a hij hki hkj]

private theorem flip_apply {N : ℕ} (a : Fin 4 → ZMod N) {i j k : Fin 4} (hij : i ≠ j) :
    flip i j a k = if k = i then -a j else if k = j then -a i else a k := by
  by_cases hki : k = i
  · subst hki; simp [flip_apply_left a hij]
  · by_cases hkj : k = j
    · subst hkj; simp [hki, flip_apply_right a hij]
    · simp [hki, hkj, flip_apply_of_ne a hij hki hkj]

private theorem negTwo_apply_left {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    negTwo i j a i = -a i := by
  rw [negTwo, swap_apply_left _ hij, flip_apply_right _ hij]

private theorem negTwo_apply_right {N : ℕ} (a : Fin 4 → ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    negTwo i j a j = -a j := by
  rw [negTwo, swap_apply_right _ hij, flip_apply_left _ hij]

private theorem negTwo_apply_of_ne {N : ℕ} (a : Fin 4 → ZMod N) {i j k : Fin 4} (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) : negTwo i j a k = a k := by
  rw [negTwo, swap_apply_of_ne _ hij hki hkj, flip_apply_of_ne _ hij hki hkj]

private theorem swap_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) {i j : Fin 4}
    (hij : i ≠ j) {a : Fin 4 → ZMod N} (ha : a ∈ S) : swap i j a ∈ S :=
  hS _ (isD4Root_single_sub_single hij) a ha

private theorem flip_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) {i j : Fin 4}
    (hij : i ≠ j) {a : Fin 4 → ZMod N} (ha : a ∈ S) : flip i j a ∈ S :=
  hS _ (isD4Root_single_add_single hij (Or.inl rfl) (Or.inl rfl)) a ha

private theorem negTwo_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) {i j : Fin 4}
    (hij : i ≠ j) {a : Fin 4 → ZMod N} (ha : a ∈ S) : negTwo i j a ∈ S :=
  swap_mem hS hij (flip_mem hS hij ha)

private theorem reflW_root_apply {N : ℕ} (a : Fin 4 → ZMod N) {p q : Fin 4} (hpq : p ≠ q)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (k : Fin 4) :
    reflW (Pi.single p s + Pi.single q t) a k =
      a k - (a p * (s : ZMod N) + a q * (t : ZMod N)) *
        (if k = p then (s : ZMod N) else if k = q then (t : ZMod N) else 0) := by
  have hβ : castW N (Pi.single p s + Pi.single q t) =
      Pi.single p (s : ZMod N) + Pi.single q (t : ZMod N) := by
    rw [castW_add N, castW_single, castW_single]
  have hdot : dotProduct a (castW N (Pi.single p s + Pi.single q t)) =
      a p * (s : ZMod N) + a q * (t : ZMod N) := by
    rw [hβ, dotProduct_add, dotProduct_single, dotProduct_single]
  rw [reflW, hdot, hβ]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hkp : k = p
  · rw [hkp]; simp [hpq]
  · by_cases hkq : k = q
    · rw [hkq]; simp [hpq, Ne.symm hpq, hkp]
    · simp [hkp, hkq]

private theorem reflW_vwt_p {N : ℕ} {p q : Fin 4} (hpq : p ≠ q) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (c : ZMod N) :
    reflW (Pi.single p s + Pi.single q t) (Pi.single p c) =
      Pi.single q (-(c * (s : ZMod N) * (t : ZMod N))) := by
  have hβ : castW N (Pi.single p s + Pi.single q t) =
      Pi.single p (s : ZMod N) + Pi.single q (t : ZMod N) := by
    rw [castW_add N, castW_single, castW_single]
  have hdot : dotProduct (Pi.single p c) (castW N (Pi.single p s + Pi.single q t)) =
      c * (s : ZMod N) := by
    rw [hβ, dotProduct_add, dotProduct_single, dotProduct_single]
    simp [Pi.single_apply, hpq]
  funext k
  rw [reflW, hdot, hβ]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
  by_cases hkp : k = p <;> by_cases hkq : k = q <;>
  simp [hkp, hkq, hpq, Pi.single_apply]

private theorem reflW_vwt_q {N : ℕ} {p q : Fin 4} (hpq : p ≠ q) {s t : ℤ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (c : ZMod N) :
    reflW (Pi.single p s + Pi.single q t) (Pi.single q c) =
      Pi.single p (-(c * (s : ZMod N) * (t : ZMod N))) := by
  have hβ : castW N (Pi.single p s + Pi.single q t) =
      Pi.single p (s : ZMod N) + Pi.single q (t : ZMod N) := by
    rw [castW_add N, castW_single, castW_single]
  have hdot : dotProduct (Pi.single q c) (castW N (Pi.single p s + Pi.single q t)) =
      c * (t : ZMod N) := by
    rw [hβ, dotProduct_add, dotProduct_single, dotProduct_single]
    simp [Pi.single_apply, hpq]
  funext k
  rw [reflW, hdot, hβ]
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
  by_cases hkp : k = p <;> by_cases hkq : k = q <;>
  simp [hkp, hkq, hpq, Pi.single_apply]

private theorem reflW_vwt_other {N : ℕ} {p q l : Fin 4} (hlp : l ≠ p) (hlq : l ≠ q)
    (hpq : p ≠ q) {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (c : ZMod N) :
    reflW (Pi.single p s + Pi.single q t) (Pi.single l c) = Pi.single l c := by
  have hβ : castW N (Pi.single p s + Pi.single q t) =
      Pi.single p (s : ZMod N) + Pi.single q (t : ZMod N) := by
    rw [castW_add N, castW_single, castW_single]
  have hdot : dotProduct (Pi.single l c) (castW N (Pi.single p s + Pi.single q t)) = 0 := by
    rw [hβ, dotProduct_add, dotProduct_single, dotProduct_single]
    simp [Pi.single_apply, Ne.symm hlp, Ne.symm hlq]
  rw [reflW, hdot, zero_smul, sub_zero]

private theorem neg_mul_units_eq {N : ℕ} {b c : ZMod N} (hc : c = b ∨ c = -b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
    -(c * (s : ZMod N) * (t : ZMod N)) = b ∨
      -(c * (s : ZMod N) * (t : ZMod N)) = -b := by
  rcases hc with rfl | rfl <;> rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
    simp

private theorem isVWt_single_neg_mul {N : ℕ} {b c : ZMod N} (hc : c = b ∨ c = -b)
    {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (q : Fin 4) :
    IsVWt b (Pi.single q (-(c * (s : ZMod N) * (t : ZMod N)))) := by
  rcases neg_mul_units_eq hc hs ht with h | h
  · exact ⟨q, Or.inl (by rw [h])⟩
  · exact ⟨q, Or.inr (by rw [h])⟩

private theorem isVWt_reflW_single {N : ℕ} {b c : ZMod N} (hc : c = b ∨ c = -b)
    {β : Fin 4 → ℤ} (hβ : IsD4Root β) {l : Fin 4} :
    IsVWt b (reflW β (Pi.single l c)) := by
  obtain ⟨p, q, hpq, hs, ht, hβeq⟩ := isD4Root_iff.mp hβ
  rw [hβeq]
  by_cases hlp : l = p
  · subst hlp
    rw [reflW_vwt_p hpq hs ht c]
    exact isVWt_single_neg_mul hc hs ht q
  · by_cases hlq : l = q
    · subst hlq
      rw [reflW_vwt_q hpq hs ht c]
      exact isVWt_single_neg_mul hc hs ht p
    · rw [reflW_vwt_other hlp hlq hpq hs ht c]
      rcases hc with rfl | rfl
      · exact ⟨l, Or.inl rfl⟩
      · exact ⟨l, Or.inr rfl⟩

theorem isVWt_reflW {N : ℕ} {b : ZMod N} {β : Fin 4 → ℤ} (hβ : IsD4Root β)
    {a : Fin 4 → ZMod N} (ha : IsVWt b a) : IsVWt b (reflW β a) := by
  obtain ⟨l, hl | hl⟩ := ha
  · rw [hl]
    exact isVWt_reflW_single (Or.inl rfl) hβ
  · rw [hl]
    exact isVWt_reflW_single (Or.inr rfl) hβ

theorem diff_card_parity {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a') :
    (Finset.univ.filter fun k => a k ≠ a' k).card % 2 =
      (negCount b a + negCount b a') % 2 := by
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  have hD : (Finset.univ.filter fun k => a k ≠ a' k).card =
      ∑ k, if a k ≠ a' k then 1 else 0 := by
    rw [Finset.card_filter]
  have hA : negCount b a = ∑ k, if a k = -b then 1 else 0 := by
    rw [negCount, Finset.card_filter]
  have hB : negCount b a' = ∑ k, if a' k = -b then 1 else 0 := by
    rw [negCount, Finset.card_filter]
  rw [hD, hA, hB, ← Finset.sum_add_distrib]
  rw [← Nat.ModEq]
  apply Nat.ModEq.sum
  intro k _
  rcases ha k with h | h <;> rcases ha' k with h' | h' <;>
  simp_all [Nat.ModEq, hbne, Ne.symm hbne] <;> omega

private theorem negCount_parity_of_flip_two {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a') {i j : Fin 4}
    (hij : i ≠ j) (hne_i : a' i ≠ a i) (hne_j : a' j ≠ a j)
    (h_eq : ∀ r, r ≠ i → r ≠ j → a r = a' r) :
    negCount b a' % 2 = negCount b a % 2 := by
  have hD : (Finset.univ.filter fun r => a r ≠ a' r) = {i, j} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hne
      by_contra hnot
      rw [not_or] at hnot
      exact hne (h_eq r hnot.1 hnot.2)
    · rintro (rfl | rfl)
      · exact Ne.symm hne_i
      · exact Ne.symm hne_j
  have hpar := diff_card_parity hN hb ha ha'
  rw [hD, Finset.card_pair hij] at hpar
  omega

private theorem isSWt_negTwo {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} (ha : IsSWt b a)
    {p q : Fin 4} (hpq : p ≠ q) : IsSWt b (negTwo p q a) := by
  intro k
  by_cases hkp : k = p
  · rw [hkp, negTwo_apply_left _ hpq]
    rcases ha p with h | h <;> simp [h]
  · by_cases hkq : k = q
    · rw [hkq, negTwo_apply_right _ hpq]
      rcases ha q with h | h <;> simp [h]
    · rw [negTwo_apply_of_ne _ hpq hkp hkq]
      exact ha k

private theorem negCount_negTwo_mod_two {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    {a : Fin 4 → ZMod N} (ha : IsSWt b a) {p q : Fin 4} (hpq : p ≠ q) :
    negCount b (negTwo p q a) % 2 = negCount b a % 2 := by
  have ha' := isSWt_negTwo ha hpq
  have hp_ne : a p ≠ 0 := by
    rcases ha p with h | h <;> simp [h, hb]
  have hq_ne : a q ≠ 0 := by
    rcases ha q with h | h <;> simp [h, hb]
  have hD : (Finset.univ.filter fun k => a k ≠ negTwo p q a k) = {p, q} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hne
      by_contra hnot
      rw [not_or] at hnot
      exact hne (by rw [negTwo_apply_of_ne _ hpq hnot.1 hnot.2])
    · rintro (rfl | rfl)
      · rw [negTwo_apply_left _ hpq]
        exact fun h => (ne_neg_of_ne_zero hN hp_ne) h
      · rw [negTwo_apply_right _ hpq]
        exact fun h => (ne_neg_of_ne_zero hN hq_ne) h
  have hpar := diff_card_parity hN hb ha ha'
  rw [hD, Finset.card_pair hpq] at hpar
  omega

theorem isSWt_reflW {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) {β : Fin 4 → ℤ}
    (hβ : IsD4Root β) {a : Fin 4 → ZMod N} (ha : IsSWt b a) :
    IsSWt b (reflW β a) ∧ negCount b (reflW β a) % 2 = negCount b a % 2 := by
  obtain ⟨p, q, hpq, hs, ht, hβeq⟩ := isD4Root_iff.mp hβ
  let s : ℤ := β p
  let t : ℤ := β q
  have hs' : s = 1 ∨ s = -1 := by simpa [s] using hs
  have ht' : t = 1 ∨ t = -1 := by simpa [t] using ht
  have hβeq' : β = Pi.single p s + Pi.single q t := by
    rw [hβeq]
  rw [hβeq']
  have hu : a p * (s : ZMod N) = b ∨ a p * (s : ZMod N) = -b := by
    rcases ha p with h | h <;> rcases hs' with h' | h' <;> rw [h, h'] <;> norm_num
  have hv : a q * (t : ZMod N) = b ∨ a q * (t : ZMod N) = -b := by
    rcases ha q with h | h <;> rcases ht' with h' | h' <;> rw [h, h'] <;> norm_num
  have hvu : a p * (s : ZMod N) = a q * (t : ZMod N) ∨
      a q * (t : ZMod N) = -(a p * (s : ZMod N)) := by
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> simp [hu, hv]
  have hs2 : (s : ZMod N) * (s : ZMod N) = 1 := by
    rcases hs' with h | h <;> rw [h] <;> norm_num
  have ht2 : (t : ZMod N) * (t : ZMod N) = 1 := by
    rcases ht' with h | h <;> rw [h] <;> norm_num
  by_cases huv : a p * (s : ZMod N) = a q * (t : ZMod N)
  · have heq : reflW (Pi.single p s + Pi.single q t) a = negTwo p q a := by
      funext k
      rw [reflW_root_apply a hpq hs' ht' k]
      by_cases hkp : k = p
      · rw [hkp, negTwo_apply_left _ hpq]
        simp
        rw [← huv]
        calc a p - (a p * (s : ZMod N) + a p * (s : ZMod N)) * (s : ZMod N)
            = a p - 2 * (a p * ((s : ZMod N) * (s : ZMod N))) := by ring
          _ = a p - 2 * a p := by rw [hs2, mul_one]
          _ = -a p := by ring
      · by_cases hkq : k = q
        · rw [hkq, negTwo_apply_right _ hpq]
          simp [Ne.symm hpq]
          rw [huv]
          calc a q - (a q * (t : ZMod N) + a q * (t : ZMod N)) * (t : ZMod N)
              = a q - 2 * (a q * ((t : ZMod N) * (t : ZMod N))) := by ring
            _ = a q - 2 * a q := by rw [ht2, mul_one]
            _ = -a q := by ring
        · rw [negTwo_apply_of_ne _ hpq hkp hkq]
          simp [hkp, hkq]
    rw [heq]
    exact ⟨isSWt_negTwo ha hpq, negCount_negTwo_mod_two hN hb ha hpq⟩
  · have hvu' : a q * (t : ZMod N) = -(a p * (s : ZMod N)) := by
      rcases hvu with h | h
      · exact absurd h huv
      · exact h
    have heq : reflW (Pi.single p s + Pi.single q t) a = a := by
      funext k
      rw [reflW_root_apply a hpq hs' ht' k]
      have hzero : a p * (s : ZMod N) + a q * (t : ZMod N) = 0 := by
        rw [hvu', add_neg_cancel]
      rw [hzero]
      by_cases hkp : k = p <;> by_cases hkq : k = q <;> simp [hkp, hkq]
    rw [heq]
    exact ⟨ha, rfl⟩

private def signAt {N : ℕ} (i : Fin 4) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  fun k => if k = i then -a k else a k

private theorem signAt_apply_self {N : ℕ} (i : Fin 4) (a : Fin 4 → ZMod N) :
    signAt i a i = -a i := by
  simp [signAt]

private theorem signAt_apply_of_ne {N : ℕ} {i k : Fin 4} (a : Fin 4 → ZMod N) (h : k ≠ i) :
    signAt i a k = a k := by
  simp [signAt, h]

private theorem negTwo_apply_of_zero {N : ℕ} {i p : Fin 4} (a : Fin 4 → ZMod N) (hip : i ≠ p)
    (hp : a p = 0) : negTwo i p a = signAt i a := by
  funext k
  by_cases hki : k = i
  · subst hki
    rw [negTwo_apply_left _ hip, signAt_apply_self]
  · by_cases hkp : k = p
    · subst hkp
      rw [negTwo_apply_right _ hip, hp, signAt_apply_of_ne _ hki, hp]
      simp
    · rw [negTwo_apply_of_ne _ hip hki hkp, signAt_apply_of_ne _ hki]

private theorem signAt_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) {i p : Fin 4}
    (hip : i ≠ p) {a : Fin 4 → ZMod N} (hp : a p = 0) (ha : a ∈ S) : signAt i a ∈ S := by
  rw [← negTwo_apply_of_zero a hip hp]
  exact negTwo_mem hS hip ha

theorem isVWt_apply_ne_zero {N : ℕ} {b : ZMod N} (hb : b ≠ 0) {a : Fin 4 → ZMod N}
    (ha : IsVWt b a) {k l : Fin 4} (hk : a k ≠ 0) (hl : a l ≠ 0) : k = l := by
  rcases ha with ⟨i, rfl | rfl⟩ <;> simp only [Pi.single_apply] at hk hl
  · by_cases hki : k = i
    · by_cases hli : l = i
      · rw [hki, hli]
      · exfalso; simpa [hli] using hl
    · exfalso; simpa [hki] using hk
  · by_cases hki : k = i
    · by_cases hli : l = i
      · rw [hki, hli]
      · exfalso; simpa [hli] using hl
    · exfalso; simpa [hki] using hk

theorem isVWt_neg_iff {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} :
    IsVWt (-b) a ↔ IsVWt b a := by
  constructor
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inr h⟩
    · exact ⟨i, Or.inl (by simpa using h)⟩
  · rintro ⟨i, h | h⟩
    · exact ⟨i, Or.inr (by simpa using h)⟩
    · exact ⟨i, Or.inl h⟩

theorem isSWt_neg_iff {N : ℕ} {b : ZMod N} {a : Fin 4 → ZMod N} :
    IsSWt (-b) a ↔ IsSWt b a := by
  constructor <;> intro h i <;> simpa only [neg_neg, or_comm] using h i

theorem negCount_neg {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    {a : Fin 4 → ZMod N} (ha : IsSWt b a) :
    negCount (-b) a = 4 - negCount b a := by
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  have hcompl : ∀ i, a i = -(-b) ↔ ¬ a i = -b := by
    intro i
    rw [neg_neg]
    constructor
    · intro h hh
      exact hbne (h.symm.trans hh)
    · intro h
      rcases ha i with h' | h'
      · exact h'
      · exact absurd h' h
  have hset : (Finset.univ.filter fun i => a i = -(-b)) =
      Finset.univ \ (Finset.univ.filter fun i => a i = -b) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    exact hcompl i
  rw [negCount, negCount, hset, Finset.card_sdiff, Finset.card_univ,
    Fintype.card_fin]
  simp

private theorem swap_single_left {N : ℕ} (b : ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    swap i j (Pi.single i b) = Pi.single j b := by
  funext k
  rw [swap_apply _ hij]
  by_cases hki : k = i
  · subst hki; simp [Pi.single_apply, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Pi.single_apply, hki, Ne.symm hij]
    · simp [Pi.single_apply, hki, hkj]

private theorem flip_single_left {N : ℕ} (b : ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    flip i j (Pi.single i b) = Pi.single j (-b) := by
  funext k
  rw [flip_apply _ hij]
  by_cases hki : k = i
  · subst hki; simp [Pi.single_apply, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Pi.single_apply, hki, Ne.symm hij]
    · simp [Pi.single_apply, hki, hkj]

private def other (i : Fin 4) : Fin 4 := if i = 0 then 1 else 0

private theorem other_ne (i : Fin 4) : other i ≠ i := by
  by_cases hi : i = 0
  · simp [other, hi]
  · simp [other, hi, Ne.symm hi]

private theorem single_mem_of_single {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {c : ZMod N} (hc : c ≠ 0) {i : Fin 4} (hi : Pi.single i c ∈ S) (j : Fin 4) :
    Pi.single j c ∈ S := by
  by_cases hij : i = j
  · simpa [hij] using hi
  · have h := swap_mem hS hij hi
    rwa [swap_single_left c hij] at h

private theorem single_neg_mem_of_single {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {c : ZMod N} (hc : c ≠ 0) {i : Fin 4} (hi : Pi.single i c ∈ S) (j : Fin 4) :
    Pi.single j (-c) ∈ S := by
  have hj : Pi.single j c ∈ S := single_mem_of_single hS hc hi j
  have hp : j ≠ other j := (other_ne j).symm
  have hk : flip j (other j) (Pi.single j c) ∈ S := flip_mem hS hp hj
  rw [flip_single_left c hp] at hk
  have h := swap_mem hS hp.symm hk
  rwa [swap_single_left (-c) hp.symm] at h

theorem isVWt_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) {b : ZMod N}
    (hb : b ≠ 0) {a a' : Fin 4 → ZMod N} (ha : IsVWt b a) (haS : a ∈ S)
    (ha' : IsVWt b a') : a' ∈ S := by
  rcases ha with ⟨i, hi | hi⟩
  · rcases ha' with ⟨j, hj | hj⟩
    · have h := single_mem_of_single hS hb (by simpa [hi] using haS) j
      rw [hj]; exact h
    · have h := single_neg_mem_of_single hS hb (by simpa [hi] using haS) j
      rw [hj]; exact h
  · have hnb : -b ≠ 0 := neg_ne_zero hb
    rcases ha' with ⟨j, hj | hj⟩
    · have h := single_neg_mem_of_single hS hnb (by simpa [hi] using haS) j
      rw [hj]; simpa using h
    · have h := single_mem_of_single hS hnb (by simpa [hi] using haS) j
      rw [hj]; exact h

private theorem swt_eq_neg_of_ne {N : ℕ} {b : ZMod N} (hbne : b ≠ -b)
    {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a') {k : Fin 4}
    (h : a k ≠ a' k) : a' k = -a k := by
  rcases ha k with hb | hb <;> rcases ha' k with hb' | hb' <;> simp_all

private theorem negTwo_pair_apply {N : ℕ} (a : Fin 4 → ZMod N) (k : Fin 4) :
    negTwo 0 1 (negTwo 2 3 a) k = -a k := by
  fin_cases k <;> simp [negTwo_apply_left, negTwo_apply_right, negTwo_apply_of_ne]

private theorem swt_eq_negTwo_of_diff_eq_pair {N : ℕ} {b : ZMod N} (hbne : b ≠ -b)
    {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a')
    {D : Finset (Fin 4)} (hD : D = Finset.univ.filter fun k => a k ≠ a' k)
    {i j : Fin 4} (hij : i ≠ j) (hDij : D = {i, j}) : a' = negTwo i j a := by
  funext k
  by_cases hki : k = i
  · subst hki
    have hkD : k ∈ D := by rw [hDij]; simp
    have hkD' : k ∈ Finset.univ.filter (fun k => a k ≠ a' k) := by
      rwa [← hD]
    have hne : a k ≠ a' k := (Finset.mem_filter.mp hkD').2
    have hneg := swt_eq_neg_of_ne hbne ha ha' hne
    rw [negTwo_apply_left _ hij]
    exact hneg
  · by_cases hkj : k = j
    · subst hkj
      have hkD : k ∈ D := by rw [hDij]; simp
      have hkD' : k ∈ Finset.univ.filter (fun k => a k ≠ a' k) := by
        rwa [← hD]
      have hne : a k ≠ a' k := (Finset.mem_filter.mp hkD').2
      have hneg := swt_eq_neg_of_ne hbne ha ha' hne
      rw [negTwo_apply_right _ hij]
      exact hneg
    · have hkD : k ∉ D := by rw [hDij]; simp [hki, hkj]
      have heq : a k = a' k := by
        by_contra hne
        exact hkD (by
          rw [hD]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      rw [negTwo_apply_of_ne _ hij hki hkj]
      exact heq.symm

private theorem swt_eq_negTwo_four_of_diff_eq_univ {N : ℕ} {b : ZMod N} (hbne : b ≠ -b)
    {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (ha' : IsSWt b a')
    {D : Finset (Fin 4)} (hD : D = Finset.univ.filter fun k => a k ≠ a' k)
    (hDuniv : D = Finset.univ) : a' = negTwo 0 1 (negTwo 2 3 a) := by
  funext k
  have hkD : k ∈ D := by rw [hDuniv]; simp
  have hkD' : k ∈ Finset.univ.filter (fun k => a k ≠ a' k) := by
    rwa [← hD]
  have hne : a k ≠ a' k := (Finset.mem_filter.mp hkD').2
  have hneg := swt_eq_neg_of_ne hbne ha ha' hne
  rw [negTwo_pair_apply]
  exact hneg

theorem isSWt_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hN : Odd N) (hS : Closed S)
    {b : ZMod N} (hb : b ≠ 0) {a a' : Fin 4 → ZMod N} (ha : IsSWt b a) (haS : a ∈ S)
    (ha' : IsSWt b a') (hpar : negCount b a % 2 = negCount b a' % 2) : a' ∈ S := by
  classical
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  let D := Finset.univ.filter fun k => a k ≠ a' k
  have hDpar : D.card % 2 = (negCount b a + negCount b a') % 2 :=
    diff_card_parity hN hb ha ha'
  have hDeven : D.card % 2 = 0 := by
    have : (negCount b a + negCount b a') % 2 = 0 := by omega
    rw [hDpar, this]
  have hDle : D.card ≤ 4 := by simpa using Finset.card_le_univ D
  have hcases : D.card = 0 ∨ D.card = 2 ∨ D.card = 4 := by omega
  have hD : D = Finset.univ.filter fun k => a k ≠ a' k := rfl
  rcases hcases with h0 | h2 | h4
  · have hDempty : D = ∅ := Finset.card_eq_zero.mp h0
    have heq : a' = a := by
      funext k
      have hk : k ∉ D := by rw [hDempty]; simp
      by_contra hne
      exact hk (by
        rw [hD]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [ne_comm] using hne⟩)
    rw [heq]; exact haS
  · obtain ⟨i, j, hij, hDij⟩ := Finset.card_eq_two.mp h2
    have hEq := swt_eq_negTwo_of_diff_eq_pair hbne ha ha' hD hij hDij
    rw [hEq]
    exact negTwo_mem hS hij haS
  · have hDuniv : D = Finset.univ := by
      apply Finset.eq_univ_of_card
      simpa using h4
    have hEq := swt_eq_negTwo_four_of_diff_eq_univ hbne ha ha' hD hDuniv
    rw [hEq]
    exact negTwo_mem hS (by decide : (0 : Fin 4) ≠ 1)
      (negTwo_mem hS (by decide : (2 : Fin 4) ≠ 3) haS)

private theorem mul_unit_ne_zero {N : ℕ} {k u : ZMod N} (hk : k ≠ 0) (hu : u = 1 ∨ u = -1) :
    k * u ≠ 0 := by
  rcases hu with rfl | rfl <;> simpa using hk

private theorem exists_ne_two {i j : Fin 4} (hij : i ≠ j) : ∃ p : Fin 4, p ≠ i ∧ p ≠ j := by
  have hcard : ({i, j} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  exact ⟨p, hp.1, hp.2⟩

private theorem isVWt_of_small_of_zero_of_ne_zero {N : ℕ} {a : Fin 4 → ZMod N} (h' : IsSmallWt a)
    {j p : Fin 4} (hj : a j ≠ 0) (hp : a p = 0) : ∃ c ≠ 0, IsVWt c a := by
  rcases h' with h0 | hV | hS
  · rw [h0] at hj; exact absurd rfl hj
  · exact hV
  · obtain ⟨c, hc, hS⟩ := hS
    rcases hS p with h | h <;> rw [hp] at h <;> exact absurd (by simpa using h.symm) hc

private theorem exists_castW_eq {N : ℕ} {α : Fin 4 → ℤ} (hα : IsD4Root α) :
    ∃ i j : Fin 4, i ≠ j ∧ ∃ u v : ZMod N,
      (u = 1 ∨ u = -1) ∧ (v = 1 ∨ v = -1) ∧
      castW N α = Pi.single i u + Pi.single j v := by
  obtain ⟨i, j, hij, hi, hj, hαeq⟩ := isD4Root_iff.mp hα
  refine ⟨i, j, hij, (α i : ZMod N), (α j : ZMod N), ?_, ?_, ?_⟩
  · rcases hi with h | h <;> simp [h]
  · rcases hj with h | h <;> simp [h]
  · rw [hαeq]
    funext k
    simp [castW, Pi.add_apply, Pi.single_apply, hij, Ne.symm hij]

private theorem add_smul_single_add_single {N : ℕ} (a : Fin 4 → ZMod N) (k u v : ZMod N)
    {i j : Fin 4} (hij : i ≠ j) :
    a + k • (Pi.single i u + Pi.single j v) =
      fun l => if l = i then a i + k * u else if l = j then a j + k * v else a l := by
  funext l
  by_cases hli : l = i
  · subst hli; simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hij]
  · by_cases hlj : l = j
    · subst hlj; simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hli, Ne.symm hij]
    · simp [Pi.add_apply, Pi.smul_apply, Pi.single_apply, hli, hlj]

private theorem add_smul_single_add_single_swap {N : ℕ} (a : Fin 4 → ZMod N)
    (k u v : ZMod N) {i j : Fin 4} (hij : i ≠ j) :
    a + k • ((Pi.single j v : Fin 4 → ZMod N) + Pi.single i u) =
      fun r => if r = j then a j + k * v else if r = i then a i + k * u else a r := by
  rw [add_comm (Pi.single j v : Fin 4 → ZMod N) (Pi.single i u)]
  funext r
  rw [add_smul_single_add_single a k u v hij]
  by_cases hrj : r = j <;> by_cases hri : r = i <;>
    simp [hrj, hri, hij, Ne.symm hij]

private theorem smul_single_add_single_apply {N : ℕ} (k u v : ZMod N) {i j : Fin 4} (hij : i ≠ j)
    (l : Fin 4) :
    (k • ((Pi.single i u : Fin 4 → ZMod N) + (Pi.single j v : Fin 4 → ZMod N))) l =
      if l = i then k * u else if l = j then k * v else 0 := by
  have h := congrFun (add_smul_single_add_single (N := N) (0 : Fin 4 → ZMod N) k u v hij) l
  simpa [mul_add] using h

theorem not_isSmallWt_step_zero {N : ℕ} {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {k : ZMod N} (hk : k ≠ 0) : ¬ IsSmallWt (k • castW N α) := by
  obtain ⟨i, j, hij, u, v, hu, hv, hcast⟩ := exists_castW_eq (N := N) hα
  have hstep : k • castW N α =
      k • ((Pi.single i u : Fin 4 → ZMod N) + (Pi.single j v : Fin 4 → ZMod N)) := by
    rw [hcast]
  have hi : (k • castW N α) i ≠ 0 := by
    rw [hstep, smul_single_add_single_apply k u v hij i]
    simp only [if_true, hij, if_false]
    rcases hu with rfl | rfl <;> simpa using hk
  have hj : (k • castW N α) j ≠ 0 := by
    rw [hstep, smul_single_add_single_apply k u v hij j]
    simp only [if_true, hij, Ne.symm hij, if_false]
    rcases hv with rfl | rfl <;> simpa using hk
  have hcard : ({i, j} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  obtain ⟨hpi, hpj⟩ := hp
  have hp0 : (k • castW N α) p = 0 := by
    rw [hstep, smul_single_add_single_apply k u v hij p]
    simp [hpi, hpj]
  intro hsmall
  rcases hsmall with hzero | hV | hS
  · rw [hzero] at hi; exact hi rfl
  · obtain ⟨c, hc, hV⟩ := hV
    exact hij (isVWt_apply_ne_zero hc hV hi hj)
  · obtain ⟨c, hc, hS⟩ := hS
    rcases hS p with h | h <;> rw [hp0] at h <;> exact hc (by simpa using h.symm)

private theorem isVWt_of_step_case_left {N : ℕ} (hN : Odd N) {k : ZMod N} (hk : k ≠ 0)
    {a a' : Fin 4 → ZMod N} {b : ZMod N} (hb : b ≠ 0) {i j : Fin 4} (hij : i ≠ j)
    {u v : ZMod N} (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hstep : a' = a + k • (Pi.single i u + Pi.single j v))
    (hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r)
    (hal : a i = b ∨ a i = -b) (ha_zero : ∀ r, r ≠ i → a r = 0)
    (h' : IsSmallWt a') : IsVWt b a' := by
  have happ : ∀ r, a' r = if r = i then a i + k * u else if r = j then a j + k * v else a r := by
    intro r; rw [hstep, hform]
  have haj : a j = 0 := ha_zero j (Ne.symm hij)
  have ha'j : a' j = k * v := by rw [happ j]; simp [Ne.symm hij, haj]
  have ha'j_ne : a' j ≠ 0 := by rw [ha'j]; exact mul_unit_ne_zero hk hv
  obtain ⟨p, hpi, hpj⟩ := exists_ne_two hij
  have ha'p : a' p = 0 := by rw [happ p]; simp [hpi, hpj, ha_zero p hpi]
  obtain ⟨c, hc, hV⟩ := isVWt_of_small_of_zero_of_ne_zero h' ha'j_ne ha'p
  have hsingle : a' = Pi.single j (a' j) := by
    rcases hV with ⟨m, hm | hm⟩
    · have hmj : m = j := by
        by_contra hne
        rw [hm] at ha'j_ne
        simp [Pi.single_apply, Ne.symm hne] at ha'j_ne
      rw [hmj] at hm
      funext r
      by_cases hrj : r = j
      · subst hrj; rw [hm]; simp
      · rw [hm]; simp [Pi.single_apply, hrj]
    · have hmj : m = j := by
        by_contra hne
        rw [hm] at ha'j_ne
        simp [Pi.single_apply, Ne.symm hne] at ha'j_ne
      rw [hmj] at hm
      funext r
      by_cases hrj : r = j
      · subst hrj; rw [hm]; simp
      · rw [hm]; simp [Pi.single_apply, hrj]
  have ha'i : a' i = 0 := by rw [hsingle]; simp [Pi.single_apply, hij]
  have hcancel : a i + k * u = 0 := by
    rw [happ i, if_pos rfl] at ha'i; exact ha'i
  have hku : k * u = -a i := eq_neg_of_add_eq_zero_right hcancel
  have hkval : k = b ∨ k = -b := by
    rcases hu with rfl | rfl
    · simp only [mul_one] at hku
      rcases hal with h | h
      · right; rw [h] at hku; exact hku
      · left; rw [h] at hku; simpa using hku
    · simp only [mul_neg, mul_one] at hku
      rcases hal with h | h
      · left; rw [h] at hku; simpa using (neg_eq_iff_eq_neg).mp hku
      · right; rw [h] at hku; simpa using (neg_eq_iff_eq_neg).mp hku
  have ha'jval : a' j = b ∨ a' j = -b := by
    rw [ha'j]
    rcases hv with rfl | rfl <;> rcases hkval with h | h <;> simp [h]
  rw [hsingle]
  rcases ha'jval with h | h
  · exact ⟨j, Or.inl (by rw [h])⟩
  · exact ⟨j, Or.inr (by rw [h])⟩

private theorem not_isSmallWt_of_three_nonzero {N : ℕ} {a : Fin 4 → ZMod N}
    {l i j : Fin 4} (hli : l ≠ i) (hlj : l ≠ j) (hij : i ≠ j)
    (hl : a l ≠ 0) (hi : a i ≠ 0) (hj : a j ≠ 0)
    (hzero : ∃ p : Fin 4, p ≠ l ∧ p ≠ i ∧ p ≠ j ∧ a p = 0) : ¬ IsSmallWt a := by
  rintro (h0 | hV | hS)
  · rw [h0] at hl; exact hl rfl
  · obtain ⟨c, hc, hV⟩ := hV
    exact hli (isVWt_apply_ne_zero hc hV hl hi)
  · obtain ⟨c, hc, hS⟩ := hS
    obtain ⟨p, hpl, hpi, hpj, hp0⟩ := hzero
    rcases hS p with h | h <;> rw [hp0] at h <;> exact hc (by simpa using h.symm)

theorem isVWt_of_step {N : ℕ} (hN : Odd N) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {k : ZMod N} (hk : k ≠ 0) {a a' : Fin 4 → ZMod N} {b : ZMod N} (hb : b ≠ 0)
    (ha : IsVWt b a) (hstep : a' = a + k • castW N α) (h' : IsSmallWt a') :
    IsVWt b a' := by
  obtain ⟨i, j, hij, u, v, hu, hv, hcast⟩ := exists_castW_eq (N := N) hα
  rw [hcast] at hstep
  have hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r :=
    add_smul_single_add_single a k u v hij
  obtain ⟨l, hl⟩ := ha
  have hal : a l = b ∨ a l = -b := by
    rcases hl with h | h <;> rw [h] <;> simp
  have ha_zero : ∀ p, p ≠ l → a p = 0 := by
    rcases hl with h | h <;> intro p hp <;> rw [h] <;> simp [Pi.single_apply, hp]
  have hal_ne : a l ≠ 0 := by rcases hal with h | h <;> simp [h, hb]
  by_cases hli : l = i
  · have hal' : a i = b ∨ a i = -b := by rw [← hli]; exact hal
    have hz' : ∀ p, p ≠ i → a p = 0 := by
      intro p hp; exact ha_zero p (by rwa [← hli] at hp)
    exact isVWt_of_step_case_left hN hk hb hij hu hv hstep hform hal' hz' h'
  · by_cases hlj : l = j
    · have hal' : a j = b ∨ a j = -b := by rw [← hlj]; exact hal
      have hz' : ∀ p, p ≠ j → a p = 0 := by
        intro p hp; exact ha_zero p (by rwa [← hlj] at hp)
      have hform' : a + k • ((Pi.single j v : Fin 4 → ZMod N) + Pi.single i u) =
          fun r => if r = j then a j + k * v else if r = i then a i + k * u else a r :=
        add_smul_single_add_single_swap a k u v hij
      have hstep' : a' = a + k • ((Pi.single j v : Fin 4 → ZMod N) + Pi.single i u) := by
        rw [add_comm (Pi.single j v : Fin 4 → ZMod N) (Pi.single i u)]
        exact hstep
      exact isVWt_of_step_case_left (i := j) (j := i) (u := v) (v := u)
        hN hk hb (Ne.symm hij) hv hu hstep' hform' hal' hz' h'
    · have hai : a i = 0 := ha_zero i (Ne.symm hli)
      have haj : a j = 0 := ha_zero j (Ne.symm hlj)
      have happ : ∀ r, a' r =
          if r = i then a i + k * u else if r = j then a j + k * v else a r := by
        intro r; rw [hstep, hform]
      have ha'l : a' l ≠ 0 := by rw [happ l]; simp [hli, hlj, hal_ne]
      have ha'i : a' i ≠ 0 := by
        rw [happ i]; simp [if_pos rfl, hai]
        exact mul_unit_ne_zero hk hu
      have ha'j : a' j ≠ 0 := by
        rw [happ j]; simp [Ne.symm hij, haj]
        exact mul_unit_ne_zero hk hv
      have hcard : ({l, i, j} : Finset (Fin 4)).card <
          (Finset.univ : Finset (Fin 4)).card := by
        have hle : ({l, i, j} : Finset (Fin 4)).card ≤ 3 := Finset.card_le_three
        rw [Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hp
      obtain ⟨hpl, hpi, hpj⟩ := hp
      have ha'p : a' p = 0 := by rw [happ p]; simp [hpl, hpi, hpj, ha_zero p hpl]
      exfalso
      exact (not_isSmallWt_of_three_nonzero hli hlj hij ha'l ha'i ha'j
        ⟨p, hpl, hpi, hpj, ha'p⟩) h'

private theorem isSWt_of_small_of_step {N : ℕ} {b : ZMod N} (hb : b ≠ 0)
    {a a' : Fin 4 → ZMod N} {i j : Fin 4} (hij : i ≠ j) {k u v : ZMod N}
    (happ : ∀ r, a' r = if r = i then a i + k * u else if r = j then a j + k * v else a r)
    (ha : IsSWt b a) (h' : IsSmallWt a') : IsSWt b a' := by
  obtain ⟨p, hpi, hpj⟩ := exists_ne_two hij
  have hcardq : ({i, j, p} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    have hle : ({i, j, p} : Finset (Fin 4)).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardq
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hq
  obtain ⟨hqi, hqj, hqp⟩ := hq
  have hap : a' p = a p := by rw [happ p]; simp [hpi, hpj]
  have haq : a' q = a q := by rw [happ q]; simp [hqi, hqj]
  have hap_ne : a' p ≠ 0 := by
    rw [hap]; rcases ha p with h | h <;> simp [h, hb]
  have haq_ne : a' q ≠ 0 := by
    rw [haq]; rcases ha q with h | h <;> simp [h, hb]
  have hqp_ne : p ≠ q := by omega
  rcases h' with h0 | hV | hS
  · rw [h0] at hap_ne; exact absurd rfl hap_ne
  · obtain ⟨c, hc, hV⟩ := hV
    exfalso
    exact hqp_ne (isVWt_apply_ne_zero hc hV hap_ne haq_ne)
  · obtain ⟨c, hc, hS⟩ := hS
    have hcp : c = b ∨ c = -b := by
      rcases ha p with hap' | hap' <;> rcases hS p with h | h
      · left; rw [← h, hap, hap']
      · right
        have : -c = b := by rw [← h, hap, hap']
        simpa using (neg_eq_iff_eq_neg).mp this
      · right; rw [← h, hap, hap']
      · left
        have : -c = -b := by rw [← h, hap, hap']
        simpa using (neg_eq_iff_eq_neg).mp this
    intro r
    rcases hS r with h | h <;> rw [h] <;> rcases hcp with hc' | hc' <;> simp [hc']

theorem isSWt_of_step {N : ℕ} (hN : Odd N) {α : Fin 4 → ℤ} (hα : IsD4Root α)
    {k : ZMod N} (hk : k ≠ 0) {a a' : Fin 4 → ZMod N} {b : ZMod N} (hb : b ≠ 0)
    (ha : IsSWt b a) (hstep : a' = a + k • castW N α) (h' : IsSmallWt a') :
    IsSWt b a' ∧ negCount b a' % 2 = negCount b a % 2 := by
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  obtain ⟨i, j, hij, u, v, hu, hv, hcast⟩ := exists_castW_eq (N := N) hα
  rw [hcast] at hstep
  have hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r :=
    add_smul_single_add_single a k u v hij
  have happ : ∀ r, a' r = if r = i then a i + k * u else if r = j then a j + k * v else a r := by
    intro r; rw [hstep, hform]
  have ha' : IsSWt b a' := isSWt_of_small_of_step hb hij happ ha h'
  have hku : k * u ≠ 0 := mul_unit_ne_zero hk hu
  have hkv : k * v ≠ 0 := mul_unit_ne_zero hk hv
  have hne_i : a' i ≠ a i := by
    rw [happ i, if_pos rfl]
    intro h
    have : k * u = 0 := by
      have h' := congrArg (fun x => x - a i) h
      simpa using h'
    exact hku this
  have hne_j : a' j ≠ a j := by
    rw [happ j]
    simp only [Ne.symm hij, if_false, if_true]
    intro h
    have : k * v = 0 := by
      have h' := congrArg (fun x => x - a j) h
      simpa using h'
    exact hkv this
  have h_eq : ∀ r, r ≠ i → r ≠ j → a r = a' r := by
    intro r hri hrj; rw [happ r]; simp [hri, hrj]
  exact ⟨ha', negCount_parity_of_flip_two hN hb ha ha' hij hne_i hne_j h_eq⟩

private theorem step_eq_case_left {N : ℕ} {k : ZMod N} {a a' : Fin 4 → ZMod N} {b : ZMod N}
    (hk : k ≠ 0) (hb : b ≠ 0) {i j : Fin 4} (hij : i ≠ j) {u v : ZMod N}
    (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1)
    (hstep : a' = a + k • (Pi.single i u + Pi.single j v))
    (hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r)
    (hal : a i = b ∨ a i = -b) (haj : a j = 0) (ha' : IsVWt b a') :
    k = b ∨ k = -b := by
  have happ : ∀ r, a' r = if r = i then a i + k * u else if r = j then a j + k * v else a r := by
    intro r; rw [hstep, hform]
  have ha'j : a' j = k * v := by rw [happ j]; simp [Ne.symm hij, haj]
  have ha'j_ne : a' j ≠ 0 := by rw [ha'j]; exact mul_unit_ne_zero hk hv
  have ha'i : a' i = 0 := by
    by_contra hne
    exact hij (isVWt_apply_ne_zero hb ha' hne ha'j_ne)
  have hcancel : a i + k * u = 0 := by
    rw [happ i, if_pos rfl] at ha'i; exact ha'i
  have hku : k * u = -a i := eq_neg_of_add_eq_zero_right hcancel
  rcases hu with rfl | rfl
  · simp only [mul_one] at hku
    rcases hal with h | h
    · right; rw [h] at hku; exact hku
    · left; rw [h] at hku; simpa using hku
  · simp only [mul_neg, mul_one] at hku
    rcases hal with h | h
    · left; rw [h] at hku; simpa using (neg_eq_iff_eq_neg).mp hku
    · right; rw [h] at hku; simpa using (neg_eq_iff_eq_neg).mp hku

theorem step_eq_of_isVWt {N : ℕ} {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ZMod N}
    (hk : k ≠ 0) {a a' : Fin 4 → ZMod N} {b : ZMod N} (hb : b ≠ 0)
    (ha : IsVWt b a) (hstep : a' = a + k • castW N α) (ha' : IsVWt b a') :
    k = b ∨ k = -b := by
  obtain ⟨i, j, hij, u, v, hu, hv, hcast⟩ := exists_castW_eq (N := N) hα
  rw [hcast] at hstep
  have hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r :=
    add_smul_single_add_single a k u v hij
  obtain ⟨l, hl⟩ := ha
  have hal : a l = b ∨ a l = -b := by
    rcases hl with h | h <;> rw [h] <;> simp
  have ha_zero : ∀ p, p ≠ l → a p = 0 := by
    rcases hl with h | h <;> intro p hp <;> rw [h] <;> simp [Pi.single_apply, hp]
  have hal_ne : a l ≠ 0 := by rcases hal with h | h <;> simp [h, hb]
  by_cases hli : l = i
  · have hal' : a i = b ∨ a i = -b := by rw [← hli]; exact hal
    have hjl : j ≠ l := by rw [hli]; exact Ne.symm hij
    have haj : a j = 0 := ha_zero j hjl
    exact step_eq_case_left hk hb hij hu hv hstep hform hal' haj ha'
  · by_cases hlj : l = j
    · have hal' : a j = b ∨ a j = -b := by rw [← hlj]; exact hal
      have hil : i ≠ l := by rw [hlj]; exact hij
      have hai : a i = 0 := ha_zero i hil
      have hform' : a + k • ((Pi.single j v : Fin 4 → ZMod N) + Pi.single i u) =
          fun r => if r = j then a j + k * v else if r = i then a i + k * u else a r :=
        add_smul_single_add_single_swap a k u v hij
      have hstep' : a' = a + k • ((Pi.single j v : Fin 4 → ZMod N) + Pi.single i u) := by
        rw [add_comm (Pi.single j v : Fin 4 → ZMod N) (Pi.single i u)]
        exact hstep
      exact step_eq_case_left (i := j) (j := i) (u := v) (v := u)
        hk hb (Ne.symm hij) hv hu hstep' hform' hal' hai ha'
    · have hai : a i = 0 := ha_zero i (Ne.symm hli)
      have happ : ∀ r, a' r =
          if r = i then a i + k * u else if r = j then a j + k * v else a r := by
        intro r; rw [hstep, hform]
      have ha'l : a' l ≠ 0 := by rw [happ l]; simp [hli, hlj, hal_ne]
      have ha'i : a' i ≠ 0 := by
        rw [happ i]; simp [if_pos rfl, hai]
        exact mul_unit_ne_zero hk hu
      exfalso
      exact hli (isVWt_apply_ne_zero hb ha' ha'l ha'i)

theorem step_eq_of_isSWt {N : ℕ} {α : Fin 4 → ℤ} (hα : IsD4Root α) {k : ZMod N}
    (hk : k ≠ 0) {a a' : Fin 4 → ZMod N} {b : ZMod N}
    (ha : IsSWt b a) (hstep : a' = a + k • castW N α) (ha' : IsSWt b a') :
    k = 2 * b ∨ k = -(2 * b) := by
  obtain ⟨i, j, hij, u, v, hu, hv, hcast⟩ := exists_castW_eq (N := N) hα
  rw [hcast] at hstep
  have hform : a + k • (Pi.single i u + Pi.single j v) =
      fun r => if r = i then a i + k * u else if r = j then a j + k * v else a r :=
    add_smul_single_add_single a k u v hij
  have happ : ∀ r, a' r = if r = i then a i + k * u else if r = j then a j + k * v else a r := by
    intro r; rw [hstep, hform]
  have happ_i : a' i = a i + k * u := by rw [happ i, if_pos rfl]
  have hku_ne : k * u ≠ 0 := mul_unit_ne_zero hk hu
  have hku : k * u = -2 * b ∨ k * u = 2 * b := by
    rcases ha i with hai | hai <;> rcases ha' i with hai' | hai' <;>
    rw [hai, hai'] at happ_i
    · exfalso
      apply hku_ne
      calc k * u = (b + k * u) - b := by ring
        _ = b - b := by rw [← happ_i]
        _ = 0 := by ring
    · left
      calc k * u = (b + k * u) - b := by ring
        _ = -b - b := by rw [← happ_i]
        _ = -2 * b := by ring
    · right
      calc k * u = (-b + k * u) - -b := by ring
        _ = b - -b := by rw [← happ_i]
        _ = 2 * b := by ring
    · exfalso
      apply hku_ne
      calc k * u = (-b + k * u) - -b := by ring
        _ = -b - -b := by rw [← happ_i]
        _ = 0 := by ring
  rcases hku with hku | hku
  · rcases hu with rfl | rfl
    · right; simpa using hku
    · left
      have : -k = -2 * b := by simpa using hku
      simpa using (neg_eq_iff_eq_neg).mp this
  · rcases hu with rfl | rfl
    · left; simpa using hku
    · right
      have : -k = 2 * b := by simpa using hku
      simpa using (neg_eq_iff_eq_neg).mp this

private theorem sign_val_eq {N : ℕ} {b : ZMod N} (hbne : b ≠ -b) {x y : Bool}
    (h : (if x then -b else b) = (if y then -b else b)) : x = y := by
  by_cases hx : x = true <;> by_cases hy : y = true <;> simp_all

private def permute {N : ℕ} (σ : Equiv.Perm (Fin 4)) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  a ∘ σ

private theorem permute_swap {N : ℕ} (i j : Fin 4) (hij : i ≠ j) (a : Fin 4 → ZMod N) :
    permute (Equiv.swap i j) a = swap i j a := by
  funext k
  rw [permute, Function.comp_apply, swap_apply _ hij]
  by_cases hki : k = i
  · subst hki; simp [hij]
  · by_cases hkj : k = j
    · subst hkj; simp [hij, Ne.symm hij]
    · simp [hki, hkj, Equiv.swap_apply_def]

private theorem permute_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    (σ : Equiv.Perm (Fin 4)) {a : Fin 4 → ZMod N} (ha : a ∈ S) : permute σ a ∈ S := by
  let motive : Equiv.Perm (Fin 4) → Prop := fun f => ∀ a, a ∈ S → permute f a ∈ S
  revert a
  change motive σ
  refine Equiv.Perm.swap_induction_on' σ ?_ ?_
  · intro a ha
    simpa [motive, permute] using ha
  · intro f x y hxy ih a ha
    have h1 : permute (f * Equiv.swap x y) a = permute (Equiv.swap x y) (permute f a) := by
      funext k; simp [permute, Equiv.Perm.mul_apply, Function.comp_apply]
    rw [h1, permute_swap x y hxy]
    exact swap_mem hS hxy (ih a ha)

private def permOfFour (i j p q : Fin 4) : Fin 4 → Fin 4 := ![i, j, p, q]

private theorem permOfFour_injective {i j p q : Fin 4} (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (hpq : p ≠ q) : Function.Injective (permOfFour i j p q) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [permOfFour]

private theorem exists_perm_four {i j p q : Fin 4} (hij : i ≠ j) (hip : i ≠ p) (hiq : i ≠ q)
    (hjp : j ≠ p) (hjq : j ≠ q) (hpq : p ≠ q) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j ∧ σ 2 = p ∧ σ 3 = q := by
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective (permOfFour i j p q)
    ((permOfFour_injective hij hip hiq hjp hjq hpq).bijective_of_finite)
  exact ⟨σ, by simp [σ, permOfFour, Equiv.ofBijective],
    by simp [σ, permOfFour, Equiv.ofBijective],
    by simp [σ, permOfFour, Equiv.ofBijective],
    by simp [σ, permOfFour, Equiv.ofBijective]⟩

private theorem exists_two_outside {i j : Fin 4} (hij : i ≠ j) :
    ∃ p q : Fin 4, p ≠ i ∧ p ≠ j ∧ q ≠ i ∧ q ≠ j ∧ q ≠ p := by
  obtain ⟨p, hpi, hpj⟩ := exists_ne_two hij
  have hcard : ({i, j, p} : Finset (Fin 4)).card < (Finset.univ : Finset (Fin 4)).card := by
    have hle : ({i, j, p} : Finset (Fin 4)).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hq
  exact ⟨p, q, hpi, hpj, hq.1, hq.2.1, hq.2.2⟩

private def signVecOn {N : ℕ} (T : Finset (Fin 4)) (s : Fin 4 → Bool) (a : Fin 4 → ZMod N) :
    Fin 4 → ZMod N :=
  fun k => if k ∈ T then (if s k then -a k else a k) else a k

private theorem signVecOn_apply {N : ℕ} {T : Finset (Fin 4)} {s : Fin 4 → Bool}
    {a : Fin 4 → ZMod N} {k : Fin 4} (hk : k ∈ T) :
    signVecOn T s a k = if s k then -a k else a k := by
  simp [signVecOn, hk]

private theorem signVecOn_apply_of_notMem {N : ℕ} {T : Finset (Fin 4)} {s : Fin 4 → Bool}
    {a : Fin 4 → ZMod N} {k : Fin 4} (hk : k ∉ T) : signVecOn T s a k = a k := by
  simp [signVecOn, hk]

private theorem signVecOn_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {T : Finset (Fin 4)} {z : Fin 4} (hzT : z ∉ T) {a : Fin 4 → ZMod N}
    (hz : a z = 0) (ha : a ∈ S) (s : Fin 4 → Bool) : signVecOn T s a ∈ S := by
  revert hzT hz ha
  refine Finset.induction_on T ?_ ?_
  · intro hzT hz ha
    have h0 : signVecOn (∅ : Finset (Fin 4)) s a = a := by
      funext k; simp [signVecOn]
    rw [h0]; exact ha
  · intro t T ht ih hzT hz ha
    have hzT' : z ∉ T := by simp only [Finset.mem_insert, not_or] at hzT; exact hzT.2
    have hzt : t ≠ z := by
      intro h; apply hzT; rw [h]; simp
    have hz' : signVecOn T s a z = 0 := by
      rw [signVecOn_apply_of_notMem hzT']; exact hz
    have hmem := ih hzT' hz ha
    by_cases hst : s t = true
    · have heq : signVecOn (insert t T) s a = signAt t (signVecOn T s a) := by
        funext k
        by_cases hkt : k = t
        · subst hkt
          simp [signVecOn, signAt, hst, ht]
        · by_cases hkT : k ∈ T
          · simp [signVecOn, signAt, hkt, hkT, hst]
          · simp [signVecOn, signAt, hkt, hkT, ht, hst]
      rw [heq]
      exact signAt_mem hS hzt hz' hmem
    · have hst' : s t = false := by simpa using hst
      have heq : signVecOn (insert t T) s a = signVecOn T s a := by
        funext k
        by_cases hkt : k = t
        · subst hkt
          simp [signVecOn, hst', ht]
        · by_cases hkT : k ∈ T
          · simp [signVecOn, hkt, hkT]
          · simp [signVecOn, hkt, hkT, ht]
      rw [heq]
      exact hmem

private theorem signVecOn_ne_zero_iff {N : ℕ} {T : Finset (Fin 4)} {a : Fin 4 → ZMod N}
    (hT : ∀ k, a k ≠ 0 ↔ k ∈ T) (s : Fin 4 → Bool) (k : Fin 4) :
    signVecOn T s a k ≠ 0 ↔ k ∈ T := by
  by_cases hk : k ∈ T
  · rw [signVecOn_apply hk]
    constructor
    · intro h
      exact hk
    · intro _
      by_cases hs : s k
      · rw [if_pos hs]; exact neg_ne_zero (hT k |>.mpr hk)
      · rw [if_neg hs]; exact hT k |>.mpr hk
  · rw [signVecOn_apply_of_notMem hk, hT k]

private theorem signVecOn_injective_on_support {N : ℕ} (hN : Odd N) {T : Finset (Fin 4)}
    {a : Fin 4 → ZMod N} (hT : ∀ k, a k ≠ 0 ↔ k ∈ T) {s s' : Fin 4 → Bool}
    (h : signVecOn T s a = signVecOn T s' a) {k : Fin 4} (hk : k ∈ T) : s k = s' k := by
  have h1 := congrFun h k
  rw [signVecOn_apply hk, signVecOn_apply hk] at h1
  exact sign_val_eq (ne_neg_of_ne_zero hN (hT k |>.mpr hk)) h1

private theorem support_eq_of_signVecOn_eq {N : ℕ} {T T' : Finset (Fin 4)}
    {a b : Fin 4 → ZMod N} (hT : ∀ k, a k ≠ 0 ↔ k ∈ T)
    (hT' : ∀ k, b k ≠ 0 ↔ k ∈ T') {s s' : Fin 4 → Bool}
    (h : signVecOn T s a = signVecOn T' s' b) : T = T' := by
  ext k
  rw [← hT k, ← hT' k]
  have hiff : signVecOn T s a k ≠ 0 ↔ signVecOn T' s' b k ≠ 0 := by rw [h]
  rw [signVecOn_ne_zero_iff hT s k, signVecOn_ne_zero_iff hT' s' k] at hiff
  rwa [← hT k, ← hT' k] at hiff

private def suppTwoT : Fin 5 → Finset (Fin 4) :=
  ![{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}]

private def suppTwoBase {N : ℕ} (b : Fin 4 → ZMod N) : Fin 5 → Fin 4 → ZMod N :=
  ![![b 0, b 1, 0, 0], ![b 0, 0, b 1, 0], ![b 0, 0, 0, b 1],
    ![0, b 1, b 0, 0], ![0, b 1, 0, b 0]]

private def suppTwoR : Fin 5 → Fin 4 := ![0, 0, 0, 1, 1]

private def suppTwoS : Fin 5 → Fin 4 := ![1, 2, 3, 2, 3]

private def suppTwoZ : Fin 5 → Fin 4 := ![2, 1, 1, 0, 0]

private def suppTwoSignFun (k : Fin 5) (br bs : Bool) (w : Fin 4) : Bool :=
  if w = suppTwoR k then br else if w = suppTwoS k then bs else false

private def suppTwoG {N : ℕ} (b : Fin 4 → ZMod N) :
    Fin 5 × Bool × Bool → Fin 4 → ZMod N := fun x =>
  signVecOn (suppTwoT x.1) (suppTwoSignFun x.1 x.2.1 x.2.2) (suppTwoBase b x.1)

private theorem suppTwoBase_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {b : Fin 4 → ZMod N} (hbS : b ∈ S) (hb2 : b 2 = 0) (hb3 : b 3 = 0) :
    ∀ k, suppTwoBase b k ∈ S := by
  have hbase0 : suppTwoBase b 0 = b := by
    funext k; fin_cases k <;> simp [suppTwoBase, hb2, hb3]
  have hbase1 : suppTwoBase b 1 = swap 1 2 b := by
    funext k; fin_cases k <;>
      simp [suppTwoBase, hb2, hb3, swap_apply, show (1 : Fin 4) ≠ 2 by decide,
        show (2 : Fin 4) ≠ 1 by decide]
  have hbase2 : suppTwoBase b 2 = swap 1 3 b := by
    funext k; fin_cases k <;>
      simp [suppTwoBase, hb2, hb3, swap_apply, show (1 : Fin 4) ≠ 3 by decide,
        show (3 : Fin 4) ≠ 1 by decide]
  have hbase3 : suppTwoBase b 3 = swap 0 2 b := by
    funext k; fin_cases k <;>
      simp [suppTwoBase, hb2, hb3, swap_apply, show (0 : Fin 4) ≠ 2 by decide,
        show (2 : Fin 4) ≠ 0 by decide]
  have hbase4 : suppTwoBase b 4 = swap 0 3 b := by
    funext k; fin_cases k <;>
      simp [suppTwoBase, hb2, hb3, swap_apply, show (0 : Fin 4) ≠ 3 by decide,
        show (3 : Fin 4) ≠ 0 by decide]
  intro k
  fin_cases k
  · change suppTwoBase b 0 ∈ S; rwa [hbase0]
  · change suppTwoBase b 1 ∈ S; rw [hbase1]; exact swap_mem hS (by decide) hbS
  · change suppTwoBase b 2 ∈ S; rw [hbase2]; exact swap_mem hS (by decide) hbS
  · change suppTwoBase b 3 ∈ S; rw [hbase3]; exact swap_mem hS (by decide) hbS
  · change suppTwoBase b 4 ∈ S; rw [hbase4]; exact swap_mem hS (by decide) hbS

private theorem suppTwoBase_zero {N : ℕ} {b : Fin 4 → ZMod N} (hb2 : b 2 = 0)
    (hb3 : b 3 = 0) : ∀ k, suppTwoBase b k (suppTwoZ k) = 0 := by
  intro k; fin_cases k <;> simp [suppTwoBase, suppTwoZ, hb2, hb3]

private theorem suppTwoZ_not_mem : ∀ k, suppTwoZ k ∉ suppTwoT k := by
  intro k; fin_cases k <;> simp [suppTwoT, suppTwoZ]

private theorem suppTwoBase_nonzero {N : ℕ} {b : Fin 4 → ZMod N} (hu : b 0 ≠ 0)
    (hv : b 1 ≠ 0) : ∀ k w, suppTwoBase b k w ≠ 0 ↔ w ∈ suppTwoT k := by
  intro k w; fin_cases k <;> fin_cases w <;> simp [suppTwoBase, suppTwoT, hu, hv]

private theorem suppTwoG_injective {N : ℕ} (hN : Odd N) {b : Fin 4 → ZMod N}
    (hu : b 0 ≠ 0) (hv : b 1 ≠ 0) : Function.Injective (suppTwoG b) := by
  rintro ⟨k, br, bs⟩ ⟨k', br', bs'⟩ h
  have hsupp : suppTwoT k = suppTwoT k' :=
    support_eq_of_signVecOn_eq (suppTwoBase_nonzero hu hv k)
      (suppTwoBase_nonzero hu hv k') h
  have hkk : k = k' := by
    by_contra hne
    have hneT : suppTwoT k ≠ suppTwoT k' := by
      fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | decide
    exact hneT hsupp
  subst hkk
  have hrr : suppTwoR k ∈ suppTwoT k := by fin_cases k <;> simp [suppTwoT, suppTwoR, suppTwoS]
  have hss : suppTwoS k ∈ suppTwoT k := by fin_cases k <;> simp [suppTwoT, suppTwoR, suppTwoS]
  have hbr : br = br' := by
    have h1 := signVecOn_injective_on_support hN (suppTwoBase_nonzero hu hv k) h hrr
    fin_cases k <;> simpa [suppTwoSignFun, suppTwoR, suppTwoS] using h1
  have hbs : bs = bs' := by
    have h1 := signVecOn_injective_on_support hN (suppTwoBase_nonzero hu hv k) h hss
    fin_cases k <;> simpa [suppTwoSignFun, suppTwoR, suppTwoS] using h1
  subst hbr hbs; rfl

private theorem card_ge_of_support_two {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) {b : Fin 4 → ZMod N} (hbS : b ∈ S) (hb2 : b 2 = 0) (hb3 : b 3 = 0)
    (hu : b 0 ≠ 0) (hv : b 1 ≠ 0) : 17 ≤ S.card := by
  have hg_mem : ∀ x : Fin 5 × Bool × Bool, suppTwoG b x ∈ S := by
    rintro ⟨k, br, bs⟩
    exact signVecOn_mem hS (suppTwoZ_not_mem k) (suppTwoBase_zero hb2 hb3 k)
      (suppTwoBase_mem hS hbS hb2 hb3 k) _
  have hsub : (Finset.univ.image (suppTwoG b)) ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
    exact hg_mem y
  have hcardimg : (Finset.univ.image (suppTwoG b)).card = 20 := by
    rw [Finset.card_image_of_injective _ (suppTwoG_injective hN hu hv), Finset.card_univ]
    simp
  have := Finset.card_le_card hsub
  omega

private def suppThreeT : Fin 3 → Finset (Fin 4) :=
  ![{0, 1, 2}, {0, 1, 3}, {0, 2, 3}]

private def suppThreeBase {N : ℕ} (b : Fin 4 → ZMod N) : Fin 3 → Fin 4 → ZMod N :=
  ![![b 0, b 1, b 2, 0], ![b 0, b 1, 0, b 2], ![b 0, 0, b 2, b 1]]

private def suppThreeR : Fin 3 → Fin 4 := ![0, 0, 0]

private def suppThreeS : Fin 3 → Fin 4 := ![1, 1, 2]

private def suppThreeT' : Fin 3 → Fin 4 := ![2, 3, 3]

private def suppThreeZ : Fin 3 → Fin 4 := ![3, 2, 1]

private def suppThreeSignFun (k : Fin 3) (s : Fin 3 → Bool) (w : Fin 4) : Bool :=
  if w = suppThreeR k then s 0 else if w = suppThreeS k then s 1
  else if w = suppThreeT' k then s 2 else false

private def suppThreeG {N : ℕ} (b : Fin 4 → ZMod N) :
    Fin 3 × (Fin 3 → Bool) → Fin 4 → ZMod N := fun x =>
  signVecOn (suppThreeT x.1) (suppThreeSignFun x.1 x.2) (suppThreeBase b x.1)

private theorem suppThreeBase_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {b : Fin 4 → ZMod N} (hbS : b ∈ S) (hb3 : b 3 = 0) :
    ∀ k, suppThreeBase b k ∈ S := by
  have hbase0 : suppThreeBase b 0 = b := by
    funext k; fin_cases k <;> simp [suppThreeBase, hb3]
  have hbase1 : suppThreeBase b 1 = swap 2 3 b := by
    funext k; fin_cases k <;>
      simp [suppThreeBase, hb3, swap_apply, show (2 : Fin 4) ≠ 3 by decide,
        show (3 : Fin 4) ≠ 2 by decide]
  have hbase2 : suppThreeBase b 2 = swap 1 3 b := by
    funext k; fin_cases k <;>
      simp [suppThreeBase, hb3, swap_apply, show (1 : Fin 4) ≠ 3 by decide,
        show (3 : Fin 4) ≠ 1 by decide]
  intro k
  fin_cases k
  · change suppThreeBase b 0 ∈ S; rwa [hbase0]
  · change suppThreeBase b 1 ∈ S; rw [hbase1]; exact swap_mem hS (by decide) hbS
  · change suppThreeBase b 2 ∈ S; rw [hbase2]; exact swap_mem hS (by decide) hbS

private theorem suppThreeBase_zero {N : ℕ} {b : Fin 4 → ZMod N} (hb3 : b 3 = 0) :
    ∀ k, suppThreeBase b k (suppThreeZ k) = 0 := by
  intro k; fin_cases k <;> simp [suppThreeBase, suppThreeZ, hb3]

private theorem suppThreeZ_not_mem : ∀ k, suppThreeZ k ∉ suppThreeT k := by
  intro k; fin_cases k <;> simp [suppThreeT, suppThreeZ]

private theorem suppThreeBase_nonzero {N : ℕ} {b : Fin 4 → ZMod N} (h0 : b 0 ≠ 0)
    (h1 : b 1 ≠ 0) (h2 : b 2 ≠ 0) :
    ∀ k w, suppThreeBase b k w ≠ 0 ↔ w ∈ suppThreeT k := by
  intro k w; fin_cases k <;> fin_cases w <;> simp [suppThreeBase, suppThreeT, h0, h1, h2]

private theorem suppThreeG_injective {N : ℕ} (hN : Odd N) {b : Fin 4 → ZMod N}
    (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0) (h2 : b 2 ≠ 0) :
    Function.Injective (suppThreeG b) := by
  rintro ⟨k, s⟩ ⟨k', s'⟩ h
  have hsupp : suppThreeT k = suppThreeT k' :=
    support_eq_of_signVecOn_eq (suppThreeBase_nonzero h0 h1 h2 k)
      (suppThreeBase_nonzero h0 h1 h2 k') h
  have hkk : k = k' := by
    by_contra hne
    have hneT : suppThreeT k ≠ suppThreeT k' := by
      fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | decide
    exact hneT hsupp
  subst hkk
  have hrrm : suppThreeR k ∈ suppThreeT k := by
    fin_cases k <;> simp [suppThreeT, suppThreeR, suppThreeS, suppThreeT']
  have hssm : suppThreeS k ∈ suppThreeT k := by
    fin_cases k <;> simp [suppThreeT, suppThreeR, suppThreeS, suppThreeT']
  have httm : suppThreeT' k ∈ suppThreeT k := by
    fin_cases k <;> simp [suppThreeT, suppThreeR, suppThreeS, suppThreeT']
  have hs0 : s 0 = s' 0 := by
    have h1 := signVecOn_injective_on_support hN (suppThreeBase_nonzero h0 h1 h2 k) h hrrm
    fin_cases k <;> simpa [suppThreeSignFun, suppThreeR, suppThreeS, suppThreeT'] using h1
  have hs1 : s 1 = s' 1 := by
    have h1 := signVecOn_injective_on_support hN (suppThreeBase_nonzero h0 h1 h2 k) h hssm
    fin_cases k <;> simpa [suppThreeSignFun, suppThreeR, suppThreeS, suppThreeT'] using h1
  have hs2 : s 2 = s' 2 := by
    have h1 := signVecOn_injective_on_support hN (suppThreeBase_nonzero h0 h1 h2 k) h httm
    fin_cases k <;> simpa [suppThreeSignFun, suppThreeR, suppThreeS, suppThreeT'] using h1
  have hss : s = s' := by funext i; fin_cases i <;> assumption
  rw [hss]

private theorem card_ge_of_support_three {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) {b : Fin 4 → ZMod N} (hbS : b ∈ S) (hb3 : b 3 = 0)
    (h0 : b 0 ≠ 0) (h1 : b 1 ≠ 0) (h2 : b 2 ≠ 0) : 17 ≤ S.card := by
  have hg_mem : ∀ x : Fin 3 × (Fin 3 → Bool), suppThreeG b x ∈ S := by
    rintro ⟨k, s⟩
    exact signVecOn_mem hS (suppThreeZ_not_mem k) (suppThreeBase_zero hb3 k)
      (suppThreeBase_mem hS hbS hb3 k) _
  have hsub : (Finset.univ.image (suppThreeG b)) ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
    exact hg_mem y
  have hcardimg : (Finset.univ.image (suppThreeG b)).card = 24 := by
    rw [Finset.card_image_of_injective _ (suppThreeG_injective hN h0 h1 h2),
      Finset.card_univ]
    simp
  have := Finset.card_le_card hsub
  omega

private def evenAct {N : ℕ} (x0 x1 x2 : Bool) (a : Fin 4 → ZMod N) : Fin 4 → ZMod N :=
  (if x0 then negTwo 0 1 else id) ((if x1 then negTwo 1 2 else id)
    ((if x2 then negTwo 2 3 else id) a))

private theorem evenAct_mem {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {a : Fin 4 → ZMod N} (ha : a ∈ S) (x0 x1 x2 : Bool) :
    evenAct x0 x1 x2 a ∈ S := by
  unfold evenAct
  rcases x0 with _ | _ <;> rcases x1 with _ | _ <;> rcases x2 with _ | _ <;>
    simp only [Bool.false_eq_true, if_false, if_true, id_eq] <;>
    first
    | exact ha
    | exact negTwo_mem hS (by decide) ha
    | exact negTwo_mem hS (by decide) (negTwo_mem hS (by decide) ha)
    | exact negTwo_mem hS (by decide) (negTwo_mem hS (by decide)
        (negTwo_mem hS (by decide) ha))

private theorem evenAct_zero {N : ℕ} (x0 x1 x2 : Bool) (a : Fin 4 → ZMod N) :
    evenAct x0 x1 x2 a 0 = if x0 then -a 0 else a 0 := by
  unfold evenAct
  rcases x0 with _ | _ <;> rcases x1 with _ | _ <;> rcases x2 with _ | _ <;>
    simp [negTwo_apply_left, negTwo_apply_right, negTwo_apply_of_ne]

private theorem evenAct_one {N : ℕ} (x0 x1 x2 : Bool) (a : Fin 4 → ZMod N) :
    evenAct x0 x1 x2 a 1 = if x0 != x1 then -a 1 else a 1 := by
  unfold evenAct
  rcases x0 with _ | _ <;> rcases x1 with _ | _ <;> rcases x2 with _ | _ <;>
    simp [negTwo_apply_left, negTwo_apply_right, negTwo_apply_of_ne]

private theorem evenAct_three {N : ℕ} (x0 x1 x2 : Bool) (a : Fin 4 → ZMod N) :
    evenAct x0 x1 x2 a 3 = if x2 then -a 3 else a 3 := by
  unfold evenAct
  rcases x0 with _ | _ <;> rcases x1 with _ | _ <;> rcases x2 with _ | _ <;>
    simp [negTwo_apply_left, negTwo_apply_right, negTwo_apply_of_ne]

private theorem evenAct_injective {N : ℕ} (hN : Odd N) {b : Fin 4 → ZMod N}
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0) :
    Function.Injective (fun x : Bool × Bool × Bool => evenAct x.1 x.2.1 x.2.2 b) := by
  rintro ⟨x0, x1, x2⟩ ⟨y0, y1, y2⟩ h
  have hz := congrFun h 0
  change evenAct x0 x1 x2 b 0 = evenAct y0 y1 y2 b 0 at hz
  rw [evenAct_zero, evenAct_zero] at hz
  have hx0 : x0 = y0 := sign_val_eq (ne_neg_of_ne_zero hN hb0) hz
  have h1 := congrFun h 1
  change evenAct x0 x1 x2 b 1 = evenAct y0 y1 y2 b 1 at h1
  rw [evenAct_one, evenAct_one, hx0] at h1
  have hxor : (y0 != x1) = (y0 != y1) := sign_val_eq (ne_neg_of_ne_zero hN hb1) h1
  have hx1 : x1 = y1 := by
    cases y0 <;> cases x1 <;> cases y1 <;> simp_all
  have h3 := congrFun h 3
  change evenAct x0 x1 x2 b 3 = evenAct y0 y1 y2 b 3 at h3
  rw [evenAct_three, evenAct_three] at h3
  have hx2 : x2 = y2 := sign_val_eq (ne_neg_of_ne_zero hN hb3) h3
  simp [hx0, hx1, hx2]

private def evenImage {N : ℕ} (b : Fin 4 → ZMod N) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.image (fun x : Bool × Bool × Bool => evenAct x.1 x.2.1 x.2.2 b)

private theorem evenImage_card {N : ℕ} (hN : Odd N) {b : Fin 4 → ZMod N}
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0) :
    (evenImage b).card = 8 := by
  rw [evenImage, Finset.card_image_of_injective _ (evenAct_injective hN hb0 hb1 hb2 hb3),
    Finset.card_univ]
  simp

private theorem swap01_nonzero {N : ℕ} {b : Fin 4 → ZMod N}
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0) :
    (swap 0 1 b) 0 ≠ 0 ∧ (swap 0 1 b) 1 ≠ 0 ∧
      (swap 0 1 b) 2 ≠ 0 ∧ (swap 0 1 b) 3 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [swap_apply_left _ (by decide : (0 : Fin 4) ≠ 1)]; exact hb1
  · rw [swap_apply_right _ (by decide : (0 : Fin 4) ≠ 1)]; exact hb0
  · rw [swap_apply_of_ne _ (by decide : (0 : Fin 4) ≠ 1) (by decide : (2 : Fin 4) ≠ 0)
      (by decide : (2 : Fin 4) ≠ 1)]; exact hb2
  · rw [swap_apply_of_ne _ (by decide : (0 : Fin 4) ≠ 1) (by decide : (3 : Fin 4) ≠ 0)
      (by decide : (3 : Fin 4) ≠ 1)]; exact hb3

private theorem evenImage_disjoint {N : ℕ} (hN : Odd N) {b : Fin 4 → ZMod N}
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0)
    (hne1 : b 0 ≠ b 1) (hne2 : b 0 ≠ -b 1) :
    Disjoint (evenImage b) (evenImage (swap 0 1 b)) := by
  rw [Finset.disjoint_left]
  intro z hzA hzB
  rcases Finset.mem_image.mp hzA with ⟨x, _, hx⟩
  rcases Finset.mem_image.mp hzB with ⟨y, _, hy⟩
  have h0 := congrFun (hx.trans hy.symm) 0
  change evenAct x.1 x.2.1 x.2.2 b 0 =
    evenAct y.1 y.2.1 y.2.2 (swap 0 1 b) 0 at h0
  rw [evenAct_zero, evenAct_zero] at h0
  rw [show (swap 0 1 b) 0 = b 1 from swap_apply_left _ (by decide : (0 : Fin 4) ≠ 1)] at h0
  have hb1ne : b 1 ≠ -b 0 := by
    intro h; apply hne2; rw [h]; simp
  by_cases hx0 : x.1 = true <;> by_cases hy0 : y.1 = true
  · simp [hx0, hy0] at h0
    exact hne1 (by simpa using h0)
  · simp [hx0, hy0] at h0
    exact hne2 (by simpa [neg_eq_iff_eq_neg] using h0)
  · simp [hx0, hy0] at h0
    exact hne2 (by simpa [neg_eq_iff_eq_neg] using h0)
  · simp [hx0, hy0] at h0
    exact hne1 (by simpa using h0)

private theorem evenImage_subset {N : ℕ} {S : Finset (Fin 4 → ZMod N)} (hS : Closed S)
    {b : Fin 4 → ZMod N} (hbS : b ∈ S) : evenImage b ⊆ S := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
  exact evenAct_mem hS hbS x.1 x.2.1 x.2.2

private theorem card_ge_of_support_four_extra {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) {b : Fin 4 → ZMod N} (hbS : b ∈ S)
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0)
    (hne1 : b 0 ≠ b 1) (hne2 : b 0 ≠ -b 1)
    {v : Fin 4 → ZMod N} (hvS : v ∈ S)
    (hvA : ∀ x : Bool × Bool × Bool, v ≠ evenAct x.1 x.2.1 x.2.2 b)
    (hvB : ∀ x : Bool × Bool × Bool, v ≠ evenAct x.1 x.2.1 x.2.2 (swap 0 1 b)) :
    17 ≤ S.card := by
  obtain ⟨hb0', hb1', hb2', hb3'⟩ := swap01_nonzero hb0 hb1 hb2 hb3
  have hAcard : (evenImage b).card = 8 := evenImage_card hN hb0 hb1 hb2 hb3
  have hBcard : (evenImage (swap 0 1 b)).card = 8 :=
    evenImage_card hN hb0' hb1' hb2' hb3'
  have hAB : Disjoint (evenImage b) (evenImage (swap 0 1 b)) :=
    evenImage_disjoint hN hb0 hb1 hb2 hb3 hne1 hne2
  have hvnotA : v ∉ evenImage b := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨x, _, hx⟩
    exact hvA x hx.symm
  have hvnotB : v ∉ evenImage (swap 0 1 b) := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨x, _, hx⟩
    exact hvB x hx.symm
  have hABv : Disjoint (evenImage b ∪ evenImage (swap 0 1 b)) {v} := by
    rw [Finset.disjoint_left]
    intro z hz hzv
    rw [Finset.mem_singleton] at hzv
    rw [hzv] at hz
    rcases Finset.mem_union.mp hz with h | h
    · exact hvnotA h
    · exact hvnotB h
  have hsub : (evenImage b ∪ evenImage (swap 0 1 b) ∪ {v}) ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact evenImage_subset hS hbS hz
      · exact evenImage_subset hS (swap_mem hS (by decide : (0 : Fin 4) ≠ 1) hbS) hz
    · rw [Finset.mem_singleton] at hz
      rwa [hz]
  have hcard17 : (evenImage b ∪ evenImage (swap 0 1 b) ∪ {v}).card = 17 := by
    rw [Finset.card_union_of_disjoint hABv, Finset.card_union_of_disjoint hAB,
      hAcard, hBcard, Finset.card_singleton]
  have := Finset.card_le_card hsub
  omega

private theorem sign_ne_of_ne {N : ℕ} {c b : ZMod N} (h1 : c ≠ b) (h2 : c ≠ -b) (x : Bool) :
    c ≠ (if x then -b else b) := by
  intro h
  by_cases hx : x = true
  · simp [hx] at h; exact h2 h
  · simp [hx] at h; exact h1 h

private theorem card_ge_of_support_four_extra02 {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) {b : Fin 4 → ZMod N} (hbS : b ∈ S)
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0)
    (hne1 : b 0 ≠ b 1) (hne2 : b 0 ≠ -b 1)
    (h2u1 : b 2 ≠ b 0) (h2u2 : b 2 ≠ -b 0) : 17 ≤ S.card := by
  have hvS : swap 0 2 b ∈ S := swap_mem hS (by decide : (0 : Fin 4) ≠ 2) hbS
  refine card_ge_of_support_four_extra hN hS hbS hb0 hb1 hb2 hb3 hne1 hne2 hvS ?_ ?_
  · intro x h
    have h0 := congrFun h 0
    change swap 0 2 b 0 = evenAct x.1 x.2.1 x.2.2 b 0 at h0
    rw [swap_apply_left _ (by decide : (0 : Fin 4) ≠ 2), evenAct_zero] at h0
    exact sign_ne_of_ne h2u1 h2u2 x.1 h0
  · intro x h
    have h1 := congrFun h 1
    change swap 0 2 b 1 = evenAct x.1 x.2.1 x.2.2 (swap 0 1 b) 1 at h1
    rw [swap_apply_of_ne _ (by decide : (0 : Fin 4) ≠ 2) (by decide : (1 : Fin 4) ≠ 0)
      (by decide : (1 : Fin 4) ≠ 2)] at h1
    rw [evenAct_one, show (swap 0 1 b) 1 = b 0 from
      swap_apply_right _ (by decide : (0 : Fin 4) ≠ 1)] at h1
    have hb1ne : b 1 ≠ b 0 := Ne.symm hne1
    have hb1ne2 : b 1 ≠ -b 0 := by
      intro hh; apply hne2; rw [hh]; simp
    exact sign_ne_of_ne hb1ne hb1ne2 (x.1 != x.2.1) h1

private theorem card_ge_of_support_four_extra12 {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) {b : Fin 4 → ZMod N} (hbS : b ∈ S)
    (hb0 : b 0 ≠ 0) (hb1 : b 1 ≠ 0) (hb2 : b 2 ≠ 0) (hb3 : b 3 ≠ 0)
    (hne1 : b 0 ≠ b 1) (hne2 : b 0 ≠ -b 1)
    (h2u : b 2 = b 0 ∨ b 2 = -b 0) : 17 ≤ S.card := by
  have h2b1 : b 2 ≠ b 1 := by
    rcases h2u with h | h <;> rw [h]
    · exact hne1
    · intro hh; exact hne2 (by simpa using congrArg Neg.neg hh)
  have h2b1' : b 2 ≠ -b 1 := by
    rcases h2u with h | h <;> rw [h]
    · intro hh; exact hne2 (by simpa using hh)
    · intro hh; exact hne1 (by simpa using congrArg Neg.neg hh)
  have hvS : swap 1 2 b ∈ S := swap_mem hS (by decide : (1 : Fin 4) ≠ 2) hbS
  refine card_ge_of_support_four_extra hN hS hbS hb0 hb1 hb2 hb3 hne1 hne2 hvS ?_ ?_
  · intro x h
    have h1 := congrFun h 1
    change swap 1 2 b 1 = evenAct x.1 x.2.1 x.2.2 b 1 at h1
    rw [swap_apply_left _ (by decide : (1 : Fin 4) ≠ 2), evenAct_one] at h1
    exact sign_ne_of_ne h2b1 h2b1' (x.1 != x.2.1) h1
  · intro x h
    have h0 := congrFun h 0
    change swap 1 2 b 0 = evenAct x.1 x.2.1 x.2.2 (swap 0 1 b) 0 at h0
    rw [swap_apply_of_ne _ (by decide : (1 : Fin 4) ≠ 2) (by decide : (0 : Fin 4) ≠ 1)
      (by decide : (0 : Fin 4) ≠ 2)] at h0
    rw [evenAct_zero, show (swap 0 1 b) 0 = b 1 from
      swap_apply_left _ (by decide : (0 : Fin 4) ≠ 1)] at h0
    exact sign_ne_of_ne hne1 hne2 x.1 h0

private def vWtOf {N : ℕ} (b : ZMod N) (p : Fin 4 × Fin 2) : Fin 4 → ZMod N :=
  if p.2 = 0 then Pi.single p.1 b else Pi.single p.1 (-b)

private theorem isVWt_vWtOf {N : ℕ} (b : ZMod N) (p : Fin 4 × Fin 2) : IsVWt b (vWtOf b p) := by
  by_cases h : p.2 = 0
  · exact ⟨p.1, Or.inl (by simp [vWtOf, h])⟩
  · exact ⟨p.1, Or.inr (by simp [vWtOf, h])⟩

private theorem vWtOf_injective {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) :
    Function.Injective (vWtOf b) := by
  rintro ⟨i, s⟩ ⟨j, t⟩ h
  simp only [vWtOf] at h
  have hnb : -b ≠ 0 := neg_ne_zero hb
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp at h ⊢
  ·
    have hij : i = j := by
      by_contra hne
      have := congrFun h i
      simp [Pi.single_apply, hne] at this
      exact hb this
    subst hij; rfl
  ·
    exfalso
    have hij : i = j := by
      by_contra hne
      have := congrFun h i
      simp [Pi.single_apply, hne] at this
      exact hb this
    subst hij
    have := congrFun h i
    simp [Pi.single_apply] at this
    exact (ne_neg_of_ne_zero hN hb) this
  ·
    exfalso
    have hij : i = j := by
      by_contra hne
      have := congrFun h i
      simp [Pi.single_apply, hne] at this
      exact hnb (by simpa using this)
    subst hij
    have := congrFun h i
    simp [Pi.single_apply] at this
    exact (ne_neg_of_ne_zero hN hb) this.symm
  ·
    have hij : i = j := by
      by_contra hne
      have := congrFun h i
      simp [Pi.single_apply, hne] at this
      exact hnb (by simpa using this)
    subst hij; rfl

theorem card_filter_isVWt {N : ℕ} [NeZero N] (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) :
    (Finset.univ.filter (IsVWt b)).card = 8 := by
  classical
  have himage : Finset.univ.filter (IsVWt b) = Finset.univ.image (vWtOf b) := by
    ext a
    constructor
    · intro ha
      rcases (Finset.mem_filter.mp ha).2 with ⟨i, hi | hi⟩
      · exact Finset.mem_image.mpr ⟨(i, 0), Finset.mem_univ _, by simp [vWtOf, hi]⟩
      · exact Finset.mem_image.mpr ⟨(i, 1), Finset.mem_univ _, by simp [vWtOf, hi]⟩
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨p, _, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, isVWt_vWtOf b p⟩
  rw [himage, Finset.card_image_of_injective _ (vWtOf_injective hN hb), Finset.card_univ]
  simp [Fintype.card_prod]

private theorem negCount_signVec {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    (s : Fin 4 → Bool) :
    negCount b (fun k => if s k then -b else b) =
      (Finset.univ.filter fun k => s k = true).card := by
  rw [negCount, Finset.card_filter, Finset.card_filter]
  congr 1
  ext k
  by_cases h : s k = true
  · simp [h]
  · simp only [h, Bool.false_eq_true, if_false, if_true, true_and, false_and]
    simp [ne_neg_of_ne_zero hN hb]

private def swtSign (e : ℕ) (s : Fin 3 → Bool) : Fin 4 → Bool :=
  let p : Bool := if e % 2 = 1 then true else false
  let x0 := s 0
  let x1 := s 1
  let x2 := s 2
  let x3 : Bool := (x0 != x1) != (x2 != p)
  fun k => if k = 0 then x0 else if k = 1 then x1 else if k = 2 then x2 else x3

private theorem swtSign_zero (e : ℕ) (s : Fin 3 → Bool) : swtSign e s 0 = s 0 := by
  simp [swtSign]

private theorem swtSign_one (e : ℕ) (s : Fin 3 → Bool) : swtSign e s 1 = s 1 := by
  simp [swtSign]

private theorem swtSign_two (e : ℕ) (s : Fin 3 → Bool) : swtSign e s 2 = s 2 := by
  simp [swtSign]

private theorem swtSign_three (e : ℕ) (s : Fin 3 → Bool) :
    swtSign e s 3 = ((s 0 != s 1) != (s 2 != (if e % 2 = 1 then true else false))) := by
  simp [swtSign]

private theorem card_filter_swtSign (e : ℕ) (s : Fin 3 → Bool) :
    (Finset.univ.filter fun k : Fin 4 => swtSign e s k = true).card % 2 = e % 2 := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  rw [swtSign_zero, swtSign_one, swtSign_two, swtSign_three]
  have hp : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hp with hp | hp <;>
  rcases s 0 with _ | _ <;> rcases s 1 with _ | _ <;> rcases s 2 with _ | _ <;>
  simp [hp]

private def swtOf {N : ℕ} (b : ZMod N) (e : ℕ) (s : Fin 3 → Bool) : Fin 4 → ZMod N :=
  fun k => if swtSign e s k then -b else b

private theorem isSWt_swtOf {N : ℕ} (b : ZMod N) (e : ℕ) (s : Fin 3 → Bool) :
    IsSWt b (swtOf b e s) := by
  intro k
  by_cases h : swtSign e s k
  · exact Or.inr (by simp [swtOf, h])
  · exact Or.inl (by simp [swtOf, h])

private theorem negCount_swtOf {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    (e : ℕ) (s : Fin 3 → Bool) :
    negCount b (swtOf b e s) % 2 = e % 2 := by
  change negCount b (fun k => if swtSign e s k then -b else b) % 2 = e % 2
  rw [negCount_signVec hN hb, card_filter_swtSign]

private theorem swtOf_injective {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) (e : ℕ) :
    Function.Injective (swtOf (N := N) b e) := by
  intro s s' h
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  funext i
  fin_cases i
  · have h0 := congrFun h 0
    dsimp [swtOf] at h0
    rw [swtSign_zero] at h0
    exact sign_val_eq hbne h0
  · have h1 := congrFun h 1
    dsimp [swtOf] at h1
    rw [swtSign_one] at h1
    exact sign_val_eq hbne h1
  · have h2 := congrFun h 2
    dsimp [swtOf] at h2
    rw [swtSign_two] at h2
    exact sign_val_eq hbne h2

private theorem swt_val_eq {N : ℕ} {b a : ZMod N} (hbne : b ≠ -b) (h : a = b ∨ a = -b) :
    (if a = -b then -b else b) = a := by
  rcases h with h | h <;> simp [h, hbne]

private theorem xor_eq_of_count_parity (s0 s1 s2 t : Bool) (e : ℕ)
    (h : (((if s0 = true then 1 else 0) + (if s1 = true then 1 else 0)
      + (if s2 = true then 1 else 0) + (if t = true then 1 else 0)) % 2 = e % 2)) :
    t = ((s0 != s1) != (s2 != (if e % 2 = 1 then true else false))) := by
  have hp : e % 2 = 0 ∨ e % 2 = 1 := by omega
  rcases hp with hp | hp <;>
  rcases s0 with _ | _ <;> rcases s1 with _ | _ <;> rcases s2 with _ | _ <;>
  rcases t with _ | _ <;> simp_all

private theorem swtOf_surjective {N : ℕ} (hN : Odd N) {b : ZMod N} (hb : b ≠ 0) (e : ℕ)
    {a : Fin 4 → ZMod N} (ha : IsSWt b a) (hpar : negCount b a % 2 = e % 2) :
    ∃ s : Fin 3 → Bool, swtOf b e s = a := by
  have hbne : b ≠ -b := ne_neg_of_ne_zero hN hb
  refine ⟨fun i => decide (a i.castSucc = -b), ?_⟩
  have hcount : negCount b a =
      (if a 0 = -b then 1 else 0) + (if a 1 = -b then 1 else 0)
      + (if a 2 = -b then 1 else 0) + (if a 3 = -b then 1 else 0) := by
    rw [negCount, Finset.card_filter, Fin.sum_univ_four]
  have hxor := xor_eq_of_count_parity (decide (a 0 = -b)) (decide (a 1 = -b))
    (decide (a 2 = -b)) (decide (a 3 = -b)) e (by
      simpa [hcount, decide_eq_true_eq] using hpar)
  funext k
  fin_cases k
  · dsimp [swtOf]
    rw [swtSign_zero]
    by_cases h0 : a 0 = -b
    · simpa [h0] using swt_val_eq hbne (ha 0)
    · have hb0 : a 0 = b := by rcases ha 0 with h' | h' <;> tauto
      simpa [h0, hb0] using swt_val_eq hbne (ha 0)
  · dsimp [swtOf]
    rw [swtSign_one]
    by_cases h1 : a 1 = -b
    · simpa [h1] using swt_val_eq hbne (ha 1)
    · have hb1 : a 1 = b := by rcases ha 1 with h' | h' <;> tauto
      simpa [h1, hb1] using swt_val_eq hbne (ha 1)
  · dsimp [swtOf]
    rw [swtSign_two]
    by_cases h2 : a 2 = -b
    · simpa [h2] using swt_val_eq hbne (ha 2)
    · have hb2 : a 2 = b := by rcases ha 2 with h' | h' <;> tauto
      simpa [h2, hb2] using swt_val_eq hbne (ha 2)
  · dsimp [swtOf]
    rw [swtSign_three]
    change (if ((decide (a 0 = -b) != decide (a 1 = -b)) !=
      (decide (a 2 = -b) != (if e % 2 = 1 then true else false))) = true then -b else b) = a 3
    rw [← hxor]
    by_cases h3 : a 3 = -b
    · simpa [h3] using swt_val_eq hbne (ha 3)
    · have hb3 : a 3 = b := by rcases ha 3 with h' | h' <;> tauto
      simpa [h3, hb3] using swt_val_eq hbne (ha 3)

theorem card_filter_isSWt {N : ℕ} [NeZero N] (hN : Odd N) {b : ZMod N} (hb : b ≠ 0)
    (e : ℕ) :
    (Finset.univ.filter fun a => IsSWt b a ∧ negCount b a % 2 = e % 2).card = 8 := by
  classical
  have hset : Finset.univ.filter (fun a => IsSWt b a ∧ negCount b a % 2 = e % 2) =
      Finset.univ.image (swtOf b e) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_filter.mp ha with ⟨_, haSWt, hpar⟩
      obtain ⟨s, rfl⟩ := swtOf_surjective hN hb e haSWt hpar
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    · intro ha
      rcases Finset.mem_image.mp ha with ⟨s, _, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, isSWt_swtOf b e s, negCount_swtOf hN hb e s⟩
  rw [hset, Finset.card_image_of_injective _ (swtOf_injective hN hb e), Finset.card_univ]
  simp

private theorem isSmallWt_of_supp_zero {N : ℕ} {a : Fin 4 → ZMod N}
    {supp : Finset (Fin 4)} (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp)
    (h0 : supp.card = 0) : IsSmallWt a := by
  left
  have hsupp_empty : supp = ∅ := Finset.card_eq_zero.mp h0
  funext i
  by_contra hne
  have hi : i ∈ supp := (hsupp i).mp hne
  rw [hsupp_empty] at hi
  simpa using hi

private theorem isSmallWt_of_supp_one {N : ℕ} {a : Fin 4 → ZMod N}
    {supp : Finset (Fin 4)} (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp)
    (h1 : supp.card = 1) : IsSmallWt a := by
  right; left
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
  have hai : a i ≠ 0 := (hsupp i).mpr (by rw [hi]; simp)
  refine ⟨a i, hai, ⟨i, Or.inl ?_⟩⟩
  funext k
  by_cases hki : k = i
  · subst hki; simp
  · have hk0 : a k = 0 := by
      by_contra hk
      have hk_supp : k ∈ supp := (hsupp k).mp hk
      rw [hi] at hk_supp
      simp [hki] at hk_supp
    simp [Pi.single_apply, hki, hk0]

private theorem false_of_supp_two {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) (hcard : S.card ≤ 16) {a : Fin 4 → ZMod N} (ha : a ∈ S)
    {supp : Finset (Fin 4)} (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp)
    (h2 : supp.card = 2) : False := by
  obtain ⟨i, j, hij, hsupp_eq⟩ := Finset.card_eq_two.mp h2
  obtain ⟨p, q, hpi, hpj, hqi, hqj, hqp⟩ := exists_two_outside hij
  have ha_zero : ∀ r, r ≠ i → r ≠ j → a r = 0 := by
    intro r hri hrj
    by_contra hr
    have hr_supp : r ∈ supp := (hsupp r).mp hr
    rw [hsupp_eq] at hr_supp
    simp [hri, hrj] at hr_supp
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := exists_perm_four hij (Ne.symm hpi) (Ne.symm hqi)
    (Ne.symm hpj) (Ne.symm hqj) (Ne.symm hqp)
  let b := permute σ a
  have hbS : b ∈ S := permute_mem hS σ ha
  have hb0 : b 0 = a i := by simp [b, permute, hσ0]
  have hb1 : b 1 = a j := by simp [b, permute, hσ1]
  have hb2 : b 2 = a p := by simp [b, permute, hσ2]
  have hb3 : b 3 = a q := by simp [b, permute, hσ3]
  have hb0n : b 0 ≠ 0 := by
    rw [hb0]; exact (hsupp i).mpr (by rw [hsupp_eq]; simp)
  have hb1n : b 1 ≠ 0 := by
    rw [hb1]; exact (hsupp j).mpr (by rw [hsupp_eq]; simp)
  have hb2z : b 2 = 0 := by rw [hb2]; exact ha_zero p hpi hpj
  have hb3z : b 3 = 0 := by rw [hb3]; exact ha_zero q hqi hqj
  have h := card_ge_of_support_two hN hS hbS hb2z hb3z hb0n hb1n
  omega

private theorem false_of_supp_three {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) (hcard : S.card ≤ 16) {a : Fin 4 → ZMod N} (ha : a ∈ S)
    {supp : Finset (Fin 4)} (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp)
    (h3 : supp.card = 3) : False := by
  obtain ⟨i, j, k, hij, hik, hjk, hsupp_eq⟩ := Finset.card_eq_three.mp h3
  have hcardp : ({i, j, k} : Finset (Fin 4)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    have hle3 : ({i, j, k} : Finset (Fin 4)).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hcardp
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hp
  obtain ⟨hpi, hpj, hpk⟩ := hp
  have ha_zero : ∀ r, r ≠ i → r ≠ j → r ≠ k → a r = 0 := by
    intro r hri hrj hrk
    by_contra hr
    have hr_supp : r ∈ supp := (hsupp r).mp hr
    rw [hsupp_eq] at hr_supp
    simp [hri, hrj, hrk] at hr_supp
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := exists_perm_four hij hik (Ne.symm hpi) hjk
    (Ne.symm hpj) (Ne.symm hpk)
  let b := permute σ a
  have hbS : b ∈ S := permute_mem hS σ ha
  have hb0 : b 0 = a i := by simp [b, permute, hσ0]
  have hb1 : b 1 = a j := by simp [b, permute, hσ1]
  have hb2 : b 2 = a k := by simp [b, permute, hσ2]
  have hb3 : b 3 = a p := by simp [b, permute, hσ3]
  have hb0n : b 0 ≠ 0 := by
    rw [hb0]; exact (hsupp i).mpr (by rw [hsupp_eq]; simp)
  have hb1n : b 1 ≠ 0 := by
    rw [hb1]; exact (hsupp j).mpr (by rw [hsupp_eq]; simp)
  have hb2n : b 2 ≠ 0 := by
    rw [hb2]; exact (hsupp k).mpr (by rw [hsupp_eq]; simp)
  have hb3z : b 3 = 0 := by rw [hb3]; exact ha_zero p hpi hpj hpk
  have h := card_ge_of_support_three hN hS hbS hb3z hb0n hb1n hb2n
  omega

private theorem exists_nonswt_pair {N : ℕ} {a : Fin 4 → ZMod N}
    (hSW : ¬ ∃ b ≠ 0, IsSWt b a) (ha0 : a 0 ≠ 0) :
    ∃ j : Fin 4, j ≠ 0 ∧ a j ≠ a 0 ∧ a j ≠ -a 0 := by
  have hnot : ¬ IsSWt (a 0) a := fun h => hSW ⟨a 0, ha0, h⟩
  rw [IsSWt] at hnot
  push Not at hnot
  obtain ⟨j, hj1, hj2⟩ := hnot
  exact ⟨j, by intro h; subst h; exact hj1 rfl, hj1, hj2⟩

private theorem false_of_supp_four_nonswt {N : ℕ} (hN : Odd N)
    {S : Finset (Fin 4 → ZMod N)} (hS : Closed S) (hcard : S.card ≤ 16)
    {a : Fin 4 → ZMod N} (ha : a ∈ S) {supp : Finset (Fin 4)}
    (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp) (hsupp_univ : supp = Finset.univ)
    (hSW : ¬ ∃ b ≠ 0, IsSWt b a) : False := by
  have ha0 : a 0 ≠ 0 := (hsupp 0).mpr (by rw [hsupp_univ]; simp)
  obtain ⟨j, hj0, hj1, hj2⟩ := exists_nonswt_pair hSW ha0
  obtain ⟨p, q, hp0, hpj, hq0, hqj, hqp⟩ := exists_two_outside (Ne.symm hj0)
  obtain ⟨σ, hσ0, hσ1, hσ2, hσ3⟩ := exists_perm_four (i := 0) (j := j) (p := p) (q := q)
    (Ne.symm hj0) (Ne.symm hp0) (Ne.symm hq0) (Ne.symm hpj) (Ne.symm hqj) (Ne.symm hqp)
  let b := permute σ a
  have hbS : b ∈ S := permute_mem hS σ ha
  have hb0 : b 0 = a 0 := by simp [b, permute, hσ0]
  have hb1 : b 1 = a j := by simp [b, permute, hσ1]
  have hb2 : b 2 = a p := by simp [b, permute, hσ2]
  have hb3 : b 3 = a q := by simp [b, permute, hσ3]
  have ha_ne : ∀ r, a r ≠ 0 := by
    intro r; exact (hsupp r).mpr (by rw [hsupp_univ]; simp)
  have hb0n : b 0 ≠ 0 := by rw [hb0]; exact ha_ne 0
  have hb1n : b 1 ≠ 0 := by rw [hb1]; exact ha_ne j
  have hb2n : b 2 ≠ 0 := by rw [hb2]; exact ha_ne p
  have hb3n : b 3 ≠ 0 := by rw [hb3]; exact ha_ne q
  have hne1 : b 0 ≠ b 1 := by rw [hb0, hb1]; exact Ne.symm hj1
  have hne2 : b 0 ≠ -b 1 := by
    rw [hb0, hb1]
    intro h
    exact hj2 (by simpa using (congrArg Neg.neg h).symm)
  by_cases h2u : b 2 = b 0 ∨ b 2 = -b 0
  · have h := card_ge_of_support_four_extra12 hN hS hbS hb0n hb1n hb2n hb3n hne1 hne2 h2u
    omega
  · push Not at h2u
    have h := card_ge_of_support_four_extra02 hN hS hbS hb0n hb1n hb2n hb3n hne1 hne2
      h2u.1 h2u.2
    omega

private theorem isSmallWt_of_supp_four {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) (hcard : S.card ≤ 16) {a : Fin 4 → ZMod N} (ha : a ∈ S)
    {supp : Finset (Fin 4)} (hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp)
    (h4 : supp.card = 4) : IsSmallWt a := by
  by_cases hSW : ∃ b ≠ 0, IsSWt b a
  · exact Or.inr (Or.inr hSW)
  · have hsupp_univ : supp = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [h4]
      simp
    exact False.elim (false_of_supp_four_nonswt hN hS hcard ha hsupp hsupp_univ hSW)

theorem isSmallWt_of_closed {N : ℕ} (hN : Odd N) {S : Finset (Fin 4 → ZMod N)}
    (hS : Closed S) (hcard : S.card ≤ 16) {a : Fin 4 → ZMod N} (ha : a ∈ S) :
    IsSmallWt a := by
  classical
  let supp := Finset.univ.filter fun i => a i ≠ 0
  have hsupp : ∀ i, a i ≠ 0 ↔ i ∈ supp := by intro i; simp [supp]
  have hle : supp.card ≤ 4 := by simpa using Finset.card_le_univ supp
  have hcases : supp.card = 0 ∨ supp.card = 1 ∨ supp.card = 2 ∨
      supp.card = 3 ∨ supp.card = 4 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4
  · exact isSmallWt_of_supp_zero hsupp h0
  · exact isSmallWt_of_supp_one hsupp h1
  · exact False.elim (false_of_supp_two hN hS hcard ha hsupp h2)
  · exact False.elim (false_of_supp_three hN hS hcard ha hsupp h3)
  · exact isSmallWt_of_supp_four hN hS hcard ha hsupp h4

end CFSG.LieType.D4Small
