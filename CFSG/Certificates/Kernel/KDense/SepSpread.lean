module

public import CFSG.Certificates.Kernel.KDense.SepTabs
public import CFSG.Certificates.Kernel.KDense.Sound

public section

namespace CFSG.KC.KDense.TabAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes
open CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371

@[expose] noncomputable def spStep (w m : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ :=
  fun k ih => Prod.rec (motive := fun _ => Nat × Nat) (fun acc t =>
    Bool.rec (motive := fun _ => Nat × Nat) (acc, t)
      (Nat.lor acc (Nat.shiftLeft (bitN m t) k), Nat.add t (nat_lit 1))
      (Nat.beq (bitN w k) (nat_lit 1))) ih

theorem bitN_toNat (x i : ℕ) : bitN x i = (x.testBit i).toNat := by
  rw [Nat.toNat_testBit]
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem spST_spec (w m : ℕ) : ∀ n,
    (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) n).2 =
        (flt (fun i => w.testBit i) n).length ∧
      ∀ y, (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) n).1.testBit y =
        (decide (y < n) && w.testBit y && m.testBit (flt (fun i => w.testBit i) y).length)
  | 0 => ⟨rfl, fun y => by simp⟩
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := spST_spec w m n
    have e : Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) (n + 1) =
        spStep w m n (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) n) :=
      rfl
    rw [e]
    generalize Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) n = s
      at ih1 ih2
    obtain ⟨acc, t⟩ := s
    simp only at ih1 ih2
    unfold spStep
    dsimp only
    have hb : Nat.beq (bitN w n) (nat_lit 1) = w.testBit n := by
      rw [bitN_toNat]
      cases w.testBit n <;> rfl
    rw [hb, flt_succ]
    cases hw : w.testBit n
    · dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      refine ⟨ih1, fun y => ?_⟩
      rw [ih2 y]
      by_cases hy : y = n
      · subst hy
        simp [hw]
      · by_cases hy' : y < n
        · simp [hy', show y < n + 1 by omega]
        · simp [hy', show ¬ y < n + 1 by omega]
    · dsimp only
      simp only [↓reduceIte, List.length_append, List.length_singleton]
      refine ⟨by rw [nadd, ih1], fun y => ?_⟩
      rw [nlor, nshl, Nat.testBit_or, ih2 y, Nat.testBit_shiftLeft, bitN_toNat, ih1]
      by_cases hy : y = n
      · subst hy
        cases hm : m.testBit (flt (fun i => w.testBit i) y).length <;> simp [hw, hm]
      · have hb : ((m.testBit (flt (fun i => w.testBit i) n).length).toNat).testBit (y - n) =
            false ∨ ¬ y ≥ n := by
          by_cases hge : y ≥ n
          · left
            cases m.testBit (flt (fun i => w.testBit i) n).length
            · simp
            · rw [Bool.toNat_true, InitAux.testBit_one]
              simp only [decide_eq_false_iff_not]
              omega
          · exact Or.inr hge
        rcases hb with hb | hb
        · rw [hb, Bool.and_false, Bool.or_false]
          by_cases hy' : y < n
          · simp [hy', show y < n + 1 by omega]
          · simp [hy', show ¬ y < n + 1 by omega]
        · rw [decide_eq_false hb, Bool.false_and, Bool.or_false]
          simp [show y < n by omega, show y < n + 1 by omega]

theorem spreadT_eq' (w m : ℕ) : spreadT w m =
    (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, nat_lit 0) (spStep w m) (nat_lit 24)).1 := by
  have e : ∀ s : ℕ × ℕ, Prod.rec (motive := fun _ => Nat) (fun acc _ => acc) s = s.1 := by
    intro s
    cases s
    rfl
  unfold spreadT
  rw [e]
  rfl

theorem testBit_combN (f : ℕ → ℕ) (a y t0 : ℕ) : ∀ n,
    (∀ t < n, t ≠ t0 → (a.testBit t && (f t).testBit y) = false) →
      (Native.combN f n a).testBit y = (decide (t0 < n) && a.testBit t0 && (f t0).testBit y)
  | 0, _ => by simp [Native.combN]
  | n + 1, h => by
    rw [Native.combN, Nat.testBit_xor, testBit_combN f a y t0 n (fun t ht => h t (by omega))]
    by_cases hn : n = t0
    · subst hn
      have : (if a.testBit n = true then f n else 0).testBit y = (a.testBit n && (f n).testBit y) := by
        cases a.testBit n <;> simp
      rw [this]
      simp
    · have h2 := h n (by omega) hn
      have : (if a.testBit n = true then f n else 0).testBit y = false := by
        cases ha : a.testBit n
        · simp
        · simpa [ha] using h2
      rw [this, Bool.xor_false]
      by_cases ht : t0 < n
      · simp [ht, show t0 < n + 1 by omega]
      · simp [ht, show ¬ t0 < n + 1 by omega]

theorem getD_of_lt {l : List ℕ} {i : ℕ} (h : i < l.length) {a : ℕ} : l.getD i a = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem suppList_eq (w : ℕ) : Native.suppList w = flt (fun i => w.testBit i) 24 := rfl

theorem spreadT_eq {w : ℕ} (hw : (flt (fun i => w.testBit i) 24).length = 8) (m : ℕ) :
    spreadT w m = Native.spreadG w m := by
  apply Nat.eq_of_testBit_eq
  intro y
  rw [spreadT_eq', (spST_spec w m (nat_lit 24)).2 y]
  unfold Native.spreadG
  rw [suppList_eq]
  by_cases hy : y < 24 ∧ w.testBit y = true
  · obtain ⟨hlt, heq⟩ := flt_index (P := fun i => w.testBit i) hy.1 hy.2
    rw [testBit_combN _ m y (flt (fun i => w.testBit i) y).length 8 (fun t ht hne => ?_)]
    · rw [decide_eq_true hy.1, hy.2, decide_eq_true (by omega), getD_of_lt (by omega),
        heq, Nat.testBit_two_pow_self]
      simp
    · have htl : t < (flt (fun i => w.testBit i) 24).length := by omega
      rw [getD_of_lt htl, Nat.testBit_two_pow]
      have := (flt_get (fun i => w.testBit i) 24 t htl).2.2
      cases hm : m.testBit t
      · rfl
      · simp only [Bool.true_and, decide_eq_false_iff_not]
        intro e
        rw [e] at this
        exact hne this.symm
  · rw [testBit_combN _ m y 8 8 (fun t ht hne => ?_)]
    · have : (decide (y < 24) && w.testBit y) = false := by
        by_cases h1 : y < 24
        · simp only [decide_eq_true h1, Bool.true_and]
          simpa [h1] using hy
        · simp [h1]
      rw [this]
      simp
    · have htl : t < (flt (fun i => w.testBit i) 24).length := by omega
      rw [getD_of_lt htl, Nat.testBit_two_pow]
      obtain ⟨h1, h2, -⟩ := flt_get (fun i => w.testBit i) 24 t htl
      cases hm : m.testBit t
      · rfl
      · simp only [Bool.true_and, decide_eq_false_iff_not]
        intro e
        rw [e] at h1 h2
        exact hy ⟨h1, h2⟩

theorem flt_length_sum (P : ℕ → Bool) : ∀ n,
    (flt P n).length = ∑ i ∈ Finset.range n, (P i).toNat
  | 0 => rfl
  | n + 1 => by
    rw [flt_succ, List.length_append, flt_length_sum P n, Finset.sum_range_succ]
    cases P n <;> simp

theorem popcN_sum : ∀ k a, Native.popcN k a = ∑ i ∈ Finset.range k, (a.testBit i).toNat
  | 0, _ => rfl
  | k + 1, a => by
    rw [Native.popcN, popcN_sum k (a / 2), Finset.sum_range_succ']
    simp only [Nat.testBit_div_two, Nat.testBit_zero]
    rw [Nat.add_comm]
    congr 1
    cases h : decide (a % 2 = 1)
    · simp at h
      simp
      omega
    · simp at h
      simp [h]

theorem flt_length_popcN (w : ℕ) : (flt (fun i => w.testBit i) 24).length = Native.popcN 24 w := by
  rw [flt_length_sum, popcN_sum]

end CFSG.KC.KDense.TabAux

end
