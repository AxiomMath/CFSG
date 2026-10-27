module

public import CFSG.GH74.BNPair.Defs

public section

namespace CFSG.GH74.BNPair

variable {W : Type*} [Group W] {J : Set W}

theorem mem_closure_iff_exists_list (hJ : ∀ s ∈ J, s * s = 1) {w : W} :
    w ∈ Subgroup.closure J ↔ ∃ l : List W, (∀ s ∈ l, s ∈ J) ∧ l.prod = w := by
  constructor
  · intro hw
    have hJJ : J ∪ J⁻¹ = J := by
      ext x
      constructor
      · rintro (h | h)
        · exact h
        · have h' : x⁻¹ ∈ J := h
          have hs : (x⁻¹)⁻¹ = x⁻¹ := inv_eq_of_mul_eq_one_right (hJ _ h')
          have hx : x = x⁻¹ := by simpa using hs
          rwa [hx]
      · intro h
        exact Or.inl h
    have h1 : w ∈ (Subgroup.closure J).toSubmonoid := hw
    rw [Subgroup.closure_toSubmonoid, hJJ] at h1
    obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure h1
    exact ⟨l, hl, hprod⟩
  · rintro ⟨l, hl, rfl⟩
    exact list_prod_mem fun s hs => Subgroup.subset_closure (hl s hs)

theorem exists_list_length_eq_wordLength (hJ : ∀ s ∈ J, s * s = 1) {w : W}
    (hw : w ∈ Subgroup.closure J) :
    ∃ l : List W, (∀ s ∈ l, s ∈ J) ∧ l.length = wordLength J w ∧ l.prod = w := by
  obtain ⟨l, hl, hprod⟩ := (mem_closure_iff_exists_list hJ).1 hw
  have hne : {k | ∃ l : List W, (∀ s ∈ l, s ∈ J) ∧ l.length = k ∧ l.prod = w}.Nonempty :=
    ⟨l.length, l, hl, rfl, hprod⟩
  exact Nat.sInf_mem hne

theorem wordLength_le {l : List W} (hl : ∀ s ∈ l, s ∈ J) : wordLength J l.prod ≤ l.length :=
  Nat.sInf_le ⟨l, hl, rfl, rfl⟩

theorem wordLength_one : wordLength J (1 : W) = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le ⟨[], by simp, rfl, by simp⟩)

theorem wordLength_eq_zero_iff (hJ : ∀ s ∈ J, s * s = 1) {w : W} (hw : w ∈ Subgroup.closure J) :
    wordLength J w = 0 ↔ w = 1 := by
  constructor
  · intro h0
    obtain ⟨l, _, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ hw
    rw [h0] at hlen
    rw [List.length_eq_zero_iff.1 hlen] at hprod
    simpa using hprod.symm
  · rintro rfl
    exact wordLength_one

theorem wordLength_mul_le (hJ : ∀ s ∈ J, s * s = 1) {a b : W} (ha : a ∈ Subgroup.closure J)
    (hb : b ∈ Subgroup.closure J) :
    wordLength J (a * b) ≤ wordLength J a + wordLength J b := by
  obtain ⟨la, hla, hlena, hproda⟩ := exists_list_length_eq_wordLength hJ ha
  obtain ⟨lb, hlb, hlenb, hprodb⟩ := exists_list_length_eq_wordLength hJ hb
  have h := wordLength_le (J := J) (l := la ++ lb) (by
    intro s hs
    rcases List.mem_append.1 hs with h | h
    · exact hla s h
    · exact hlb s h)
  rw [List.prod_append, hproda, hprodb, List.length_append, hlena, hlenb] at h
  exact h

theorem wordLength_gen_le_one {s : W} (hs : s ∈ J) :
    wordLength J s ≤ 1 := by
  have := wordLength_le (J := J) (l := [s]) (by simpa using hs)
  simpa using this

theorem wordLength_gen_mul_le (hJ : ∀ s ∈ J, s * s = 1) {s w : W} (hs : s ∈ J)
    (hw : w ∈ Subgroup.closure J) : wordLength J (s * w) ≤ wordLength J w + 1 := by
  have h := wordLength_mul_le hJ (Subgroup.subset_closure hs) hw
  have h1 := wordLength_gen_le_one hs
  omega

theorem wordLength_mul_gen_le (hJ : ∀ s ∈ J, s * s = 1) {s w : W} (hs : s ∈ J)
    (hw : w ∈ Subgroup.closure J) : wordLength J (w * s) ≤ wordLength J w + 1 := by
  have h := wordLength_mul_le hJ hw (Subgroup.subset_closure hs)
  have h1 := wordLength_gen_le_one hs
  omega

theorem exists_left_descent (hJ : ∀ s ∈ J, s * s = 1) {w : W} (hw : w ∈ Subgroup.closure J)
    (hw1 : w ≠ 1) : ∃ s ∈ J, wordLength J (s * w) + 1 = wordLength J w := by
  obtain ⟨l, hl, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ hw
  cases l with
  | nil =>
    exact absurd (by simpa using hprod.symm) hw1
  | cons s l' =>
    have hs : s ∈ J := hl s (by simp)
    have hl' : ∀ t ∈ l', t ∈ J := fun t ht => hl t (by simp [ht])
    refine ⟨s, hs, ?_⟩
    have h1 : s * w = l'.prod := by
      rw [← hprod, List.prod_cons, ← mul_assoc, hJ s hs, one_mul]
    have h2 : wordLength J (s * w) ≤ l'.length := by
      rw [h1]
      exact wordLength_le hl'
    have h3 : wordLength J w ≤ wordLength J (s * w) + 1 := by
      have := wordLength_gen_mul_le hJ hs (Subgroup.mul_mem _ (Subgroup.subset_closure hs) hw)
      rwa [← mul_assoc, hJ s hs, one_mul] at this
    simp only [List.length_cons] at hlen
    omega

theorem exists_right_descent (hJ : ∀ s ∈ J, s * s = 1) {w : W} (hw : w ∈ Subgroup.closure J)
    (hw1 : w ≠ 1) : ∃ s ∈ J, wordLength J (w * s) + 1 = wordLength J w := by
  obtain ⟨l, hl, hlen, hprod⟩ := exists_list_length_eq_wordLength hJ hw
  rcases List.eq_nil_or_concat l with rfl | ⟨L, s, rfl⟩
  · exact absurd (by simpa using hprod.symm) hw1
  · have hs : s ∈ J := hl s (by simp)
    have hL : ∀ t ∈ L, t ∈ J := fun t ht => hl t (by simp [ht])
    refine ⟨s, hs, ?_⟩
    have h1 : w * s = L.prod := by
      rw [← hprod, List.prod_concat, mul_assoc, hJ s hs, mul_one]
    have h2 : wordLength J (w * s) ≤ L.length := by
      rw [h1]
      exact wordLength_le hL
    have h3 : wordLength J w ≤ wordLength J (w * s) + 1 := by
      have := wordLength_mul_gen_le hJ hs (Subgroup.mul_mem _ hw (Subgroup.subset_closure hs))
      rwa [mul_assoc, hJ s hs, mul_one] at this
    simp only [List.length_concat] at hlen
    omega

end CFSG.GH74.BNPair
