module

public import CFSG.FeitThompson.Representations.GramArrayLineNoOppositeSigns
public import CFSG.FeitThompson.Representations.IntegerVectorSquaredLengthThree
import CFSG.FeitThompson.Representations.FourRowsCommonColumnCoordinate

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Finset Matrix

theorem eq_of_mul_nonneg_of_eq_one_or_neg_one {x y : ℤ} (hx : x = 1 ∨ x = -1)
    (hy : y = 1 ∨ y = -1) (h : 0 ≤ x * y) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

theorem exists_ne_three_of_four_le {m : ℕ} (hm : 4 ≤ m) (i₁ i₂ i₃ : Fin m) :
    ∃ i₄ : Fin m, i₁ ≠ i₄ ∧ i₂ ≠ i₄ ∧ i₃ ≠ i₄ := by
  classical
  have h1 := Finset.card_insert_le i₁ ({i₂, i₃} : Finset (Fin m))
  have h2 := Finset.card_insert_le i₂ ({i₃} : Finset (Fin m))
  simp only [Finset.card_singleton] at h2
  have hle : #({i₁, i₂, i₃} : Finset (Fin m)) ≤ 3 := by omega
  have hne : ({i₁, i₂, i₃} : Finset (Fin m)) ≠ Finset.univ := by
    intro h
    rw [h, Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨i₄, hi₄⟩ := not_forall.mp (fun h => hne (Finset.eq_univ_iff_forall.mpr h))
  refine ⟨i₄, fun h => hi₄ ?_, fun h => hi₄ ?_, fun h => hi₄ ?_⟩ <;> subst h <;> simp

theorem exists_three_ne_of_four_le {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    ∃ r₁ r₂ r₃ : Fin m, r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ ∧ r₁ ≠ i ∧ r₂ ≠ i ∧ r₃ ≠ i := by
  classical
  have hcard : 3 ≤ #(({i} : Finset (Fin m))ᶜ) := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨t, hts, ht3⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨r₁, r₂, r₃, h12, h13, h23, rfl⟩ := Finset.card_eq_three.mp ht3
  have hne : ∀ r ∈ ({r₁, r₂, r₃} : Finset (Fin m)), r ≠ i := by
    intro r hr
    simpa using hts hr
  exact ⟨r₁, r₂, r₃, h12, h13, h23, hne _ (by simp), hne _ (by simp), hne _ (by simp)⟩

theorem exists_isSignedCoordVec_dotProduct_eq_delta {d m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) (j : Fin n) :
    ∃ c : Fin d → ℤ, IsSignedCoordVec c ∧
      ∀ (i : Fin m) (k : Fin n), b i k ⬝ᵥ c = if k = j then 1 else 0 := by
  classical
  have hm2 : 2 ≤ m := by omega
  have h12 : (⟨0, by omega⟩ : Fin m) ≠ (⟨1, by omega⟩ : Fin m) := by simp [Fin.ext_iff]
  set i₁ : Fin m := ⟨0, by omega⟩
  set i₂ : Fin m := ⟨1, by omega⟩
  obtain ⟨a, ha, ha12, ha1⟩ := exists_support_inter_eq_singleton_of_isGramArray_fin hm2 hn hb
    (i := i₁) (j := j) (k := i₂) (l := j) (by simp [h12]) (Or.inr rfl)
  obtain ⟨s, hs, hs1⟩ : ∃ s : ℤ, b i₁ j a = s ∧ (s = 1 ∨ s = -1) := ⟨_, rfl, ha1⟩
  have hs0 : s ≠ 0 := by rcases hs1 with h | h <;> simp [h]
  have hcol : ∀ i : Fin m, b i j a = s := by
    intro i
    by_cases hii : i = i₁
    · rw [hii, hs]
    have hne0 : b i j a ≠ 0 := by
      by_cases hii2 : i = i₂
      · rw [hii2, ← ha12, hs]; exact hs0
      · obtain ⟨i₄, hq1, hq2, hq3⟩ := exists_ne_three_of_four_le hm i₁ i₂ i
        exact hb.mem_support_of_four_rows hn h12 (Ne.symm hii) hq1 (Ne.symm hii2) hq2 hq3 j ha
    have hsign : 0 ≤ b i j a * s :=
      hs ▸ mul_nonneg_of_isGramArray_fin hm2 hn hb (i := i) (j := j) (k := i₁) (l := j)
        (by simp [hii]) (Or.inr rfl) a
    exact eq_of_mul_nonneg_of_eq_one_or_neg_one
      (eq_one_or_neg_one_of_dotProduct_self_eq_three (hb.dotProduct_self i j) hne0) hs1 hsign
  have hshare : ∀ r r' : Fin m, r ≠ r' → ∀ c : Fin d, b r j c ≠ 0 → b r' j c ≠ 0 → c = a := by
    intro r r' hrr c hc hc'
    obtain ⟨a', ha', -, -⟩ := exists_support_inter_eq_singleton_of_isGramArray_fin hm2 hn hb
      (i := r) (j := j) (k := r') (l := j) (by simp [hrr]) (Or.inr rfl)
    have hmem : ∀ x : Fin d, (b r j x ≠ 0 ∧ b r' j x ≠ 0) ↔ x = a' := by
      intro x
      simpa [Function.mem_support] using Set.ext_iff.mp ha' x
    rw [(hmem c).mp ⟨hc, hc'⟩, (hmem a).mp ⟨by rw [hcol r]; exact hs0, by rw [hcol r']; exact hs0⟩]
  have hoth : ∀ (i : Fin m) (k : Fin n), k ≠ j → b i k a = 0 := by
    intro i k hkj
    by_contra hik0
    have hsign : 0 ≤ b i k a * s :=
      hcol i ▸ mul_nonneg_of_isGramArray_fin hm2 hn hb (i := i) (j := k) (k := i) (l := j)
        (by simp [hkj]) (Or.inl rfl) a
    have hika : b i k a = s := eq_of_mul_nonneg_of_eq_one_or_neg_one
      (eq_one_or_neg_one_of_dotProduct_self_eq_three (hb.dotProduct_self i k) hik0) hs1 hsign
    have key : ∀ r : Fin m, r ≠ i → ∃ c, c ≠ a ∧ b r j c ≠ 0 ∧ b i k c ≠ 0 := by
      intro r hr
      have hzero : ∑ c : Fin d, b r j c * b i k c = 0 := hb.dotProduct_eq_zero hr (Ne.symm hkj)
      have hsplit := Finset.sum_erase_add (univ : Finset (Fin d))
        (fun c => b r j c * b i k c) (mem_univ a)
      rw [hzero, hcol r, hika] at hsplit
      have hsum : ∑ c ∈ (univ : Finset (Fin d)).erase a, b r j c * b i k c ≠ 0 := by
        rcases hs1 with h | h <;> rw [h] at hsplit <;> intro hc <;> rw [hc] at hsplit <;> omega
      obtain ⟨c, hcmem, hcne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      exact ⟨c, (Finset.mem_erase.mp hcmem).1, left_ne_zero_of_mul hcne,
        right_ne_zero_of_mul hcne⟩
    obtain ⟨r₁, r₂, r₃, hr12, hr13, hr23, hri1, hri2, hri3⟩ := exists_three_ne_of_four_le hm i
    obtain ⟨c₁, hc₁a, hc₁r, hc₁⟩ := key r₁ hri1
    obtain ⟨c₂, hc₂a, hc₂r, hc₂⟩ := key r₂ hri2
    obtain ⟨c₃, hc₃a, hc₃r, hc₃⟩ := key r₃ hri3
    have hc12 : c₁ ≠ c₂ := fun h => hc₁a (hshare r₁ r₂ hr12 c₁ hc₁r (h ▸ hc₂r))
    have hc13 : c₁ ≠ c₃ := fun h => hc₁a (hshare r₁ r₃ hr13 c₁ hc₁r (h ▸ hc₃r))
    have hc23 : c₂ ≠ c₃ := fun h => hc₂a (hshare r₂ r₃ hr23 c₂ hc₂r (h ▸ hc₃r))
    have hcard4 : #({a, c₁, c₂, c₃} : Finset (Fin d)) = 4 := by
      rw [Finset.card_insert_of_notMem
          (by simp [Ne.symm hc₁a, Ne.symm hc₂a, Ne.symm hc₃a]),
        Finset.card_insert_of_notMem (by simp [hc12, hc13]),
        Finset.card_insert_of_notMem (by simp [hc23]), Finset.card_singleton]
    have hsub : ({a, c₁, c₂, c₃} : Finset (Fin d)) ⊆
        ({x | b i k x ≠ 0} : Finset (Fin d)) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl | rfl
      · exact hik0
      · exact hc₁
      · exact hc₂
      · exact hc₃
    have hcard3 : #({x | b i k x ≠ 0} : Finset (Fin d)) = 3 :=
      card_support_eq_three_of_dotProduct_self_eq_three (hb.dotProduct_self i k)
    have := Finset.card_le_card hsub
    omega
  refine ⟨sharedSignedCoord (b i₁ j) a, isSignedCoordVec_sharedSignedCoord ha1, ?_⟩
  intro i k
  rw [dotProduct_sharedSignedCoord, hs]
  by_cases hkj : k = j
  · subst hkj
    rw [if_pos rfl, hcol i]
    rcases hs1 with h | h <;> simp [h]
  · rw [if_neg hkj, hoth i k hkj, zero_mul]

theorem exists_pivot_family {d m n : ℕ} (hm : 4 ≤ m) (hn : 2 ≤ n)
    {b : Fin m → Fin n → Fin d → ℤ} (hb : IsGramArray b) :
    ∃ c : Fin n → Fin d → ℤ, (∀ j, IsSignedCoordVec (c j)) ∧
      ∀ (i : Fin m) (k j : Fin n), b i k ⬝ᵥ c j = if k = j then 1 else 0 := by
  choose c hc hdot using fun j => exists_isSignedCoordVec_dotProduct_eq_delta hm hn hb j
  exact ⟨c, hc, fun i k j => hdot j i k⟩

end CFSG.FeitThompson
