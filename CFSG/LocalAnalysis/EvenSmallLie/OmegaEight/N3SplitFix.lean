module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native

public section

namespace CFSG.EvenSmallLie.OmegaEight.N3Split

open CFSG.EvenSmallLie.OmegaEight.Stage2

theorem xor_two_pow_eq_add {w j : ℕ} (h : w < 2 ^ j) : w ^^^ 2 ^ j = w + 2 ^ j := by
  rw [← Nat.or_two_pow_eq_add_of_lt h]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases hij : j = i
  · subst hij
    rw [Nat.testBit_lt_two_pow h]
    simp
  · simp [hij]

@[expose] def dblTab (T : Array ℕ) (c : ℕ) : Array ℕ := T ++ T.map (· ^^^ c)

@[expose] def imgTab (k : ℕ) : ℕ → Array ℕ
  | 0 => #[0]
  | j + 1 => dblTab (imgTab k j) (mulVecK k (2 ^ j))

theorem imgTab_size (k : ℕ) : ∀ j, (imgTab k j).size = 2 ^ j
  | 0 => rfl
  | j + 1 => by
    rw [imgTab, dblTab, Array.size_append, Array.size_map, imgTab_size k j, pow_succ]
    ring

theorem imgTab_getD (k : ℕ) : ∀ j v, v < 2 ^ j → (imgTab k j).getD v 0 = mulVecK k v
  | 0, v, hv => by
    have hv0 : v = 0 := by simpa using hv
    subst hv0
    rw [mulVecK_zero]
    rfl
  | j + 1, v, hv => by
    rw [imgTab, dblTab, Array.getD_eq_getD_getElem?]
    by_cases hvj : v < 2 ^ j
    · rw [Array.getElem?_append_left (by rw [imgTab_size]; exact hvj),
        ← Array.getD_eq_getD_getElem?, imgTab_getD k j v hvj]
    · have hle : (imgTab k j).size ≤ v := by rw [imgTab_size]; omega
      rw [Array.getElem?_append_right hle, Array.getElem?_map, imgTab_size]
      have hw : v - 2 ^ j < 2 ^ j := by rw [pow_succ] at hv; omega
      have e := imgTab_getD k j (v - 2 ^ j) hw
      rw [Array.getD_eq_getD_getElem?] at e
      rcases h : (imgTab k j)[v - 2 ^ j]? with _ | x
      · rw [h] at e
        rw [Array.getElem?_eq_none_iff, imgTab_size] at h
        omega
      · rw [h] at e
        simp only [Option.map_some, Option.getD_some] at e ⊢
        rw [e, ← mulVecK_xor, xor_two_pow_eq_add hw, Nat.sub_add_cancel (by omega)]

@[expose] def fixVecs (k : ℕ) : List ℕ :=
  let T := imgTab k 12
  (List.range 4096).filter fun v => T.getD v 0 == v

theorem mem_fixVecs {k v : ℕ} : v ∈ fixVecs k ↔ v < 4096 ∧ mulVecK k v = v := by
  have h : ∀ n, (∀ w < n, (imgTab k 12).getD w 0 = mulVecK k w) →
      ((v ∈ (List.range n).filter fun w => (imgTab k 12).getD w 0 == w) ↔
        v < n ∧ mulVecK k v = v) := by
    intro n hn
    rw [List.mem_filter, List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨hv, e⟩
      exact ⟨hv, by rwa [hn v hv] at e⟩
    · rintro ⟨hv, e⟩
      exact ⟨hv, by rwa [hn v hv]⟩
  exact h 4096 fun w hw => imgTab_getD k 12 w hw

theorem nodup_fixVecs (k : ℕ) : (fixVecs k).Nodup := List.nodup_range.filter _

@[expose] def fixCountF (k : ℕ) : ℕ := (fixVecs k).length

theorem fixCountF_eq (k : ℕ) : fixCountF k = fixCount k := by
  have e : (fixVecs k).toFinset = (Finset.range 4096).filter fun v => mulVecK k v = v := by
    ext v
    rw [List.mem_toFinset, mem_fixVecs, Finset.mem_filter, Finset.mem_range]
  rw [fixCountF, fixCount, ← List.toFinset_card_of_nodup (nodup_fixVecs k), e]

end CFSG.EvenSmallLie.OmegaEight.N3Split
